import EffectSemantics.Recursive.Fixpoint

namespace EffectSemantics

/-- Deterministic head classification, including malformed closed terms. -/
inductive Head where
  | returned (value : Val)
  | internal (next : Comp)
  | base (request : BaseRequest)
  | free (request : FreeRequest)
  | stuck
  deriving DecidableEq, Repr

def Comp.head : Comp → Head
  | .ret value => .returned value
  | .letE bound body =>
      match bound.head with
      | .returned value => .internal (body.subst0 value)
      | .internal next => .internal (.letE next body)
      | .base request => .base (request.outerLet body)
      | .free request => .free (request.outerLet body)
      | .stuck => .stuck
  | .app (.lam _ _ body) argument => .internal (body.subst0 argument)
  | .app (.fixLam domain latent body) argument =>
      .internal (body.subst2 argument (.fixLam domain latent body))
  | .app _ _ => .stuck
  | .ite (.bool true) thenBranch _ => .internal thenBranch
  | .ite (.bool false) _ elseBranch => .internal elseBranch
  | .ite _ _ _ => .stuck
  | .case (.inl value _) leftBranch _ =>
      .internal (leftBranch.subst0 value)
  | .case (.inr _ value) _ rightBranch =>
      .internal (rightBranch.subst0 value)
  | .case _ _ _ => .stuck
  | .baseOp operation parameter =>
      .base ⟨operation, parameter, []⟩
  | .freeOp interface operation parameter =>
      .free ⟨interface, operation, parameter, []⟩

inductive FiniteOutcome where
  | returned (value : Val)
  | base (request : BaseRequest)
  | free (request : FreeRequest)
  deriving DecidableEq, Repr

/-- The `fuel`-th finite observation. Internal CBV reductions consume fuel;
visible return/request heads do not need an additional recursive call. -/
def Comp.observe : Nat → Comp → Option FiniteOutcome
  | 0, _ => none
  | fuel + 1, term =>
      match term.head with
      | .returned value => some (.returned value)
      | .internal next => next.observe fuel
      | .base request => some (.base request)
      | .free request => some (.free request)
      | .stuck => none

theorem Step.to_head {term next : Comp} (step : Step term next) :
    term.head = .internal next := by
  induction step with
  | letReturn => rfl
  | beta => rfl
  | fixBeta => rfl
  | ifTrue => rfl
  | ifFalse => rfl
  | caseInl => rfl
  | caseInr => rfl
  | underLet inner ih => simp [Comp.head, ih]

theorem EvalContext.plug_head_base (context : EvalContext)
    (head : term.head = .base request) :
    (context.plug term).head = .base { request with
      context := request.context ++ context } := by
  induction context generalizing term request with
  | nil => simpa using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          rw [EvalContext.plug_cons]
          have inner : (Comp.letE term body).head =
              .base (request.outerLet body) := by
            simp [Comp.head, head]
          simpa [Frame.plug, BaseRequest.outerLet, List.append_assoc] using ih inner

theorem EvalContext.plug_head_free (context : EvalContext)
    (head : term.head = .free request) :
    (context.plug term).head = .free { request with
      context := request.context ++ context } := by
  induction context generalizing term request with
  | nil => simpa using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          rw [EvalContext.plug_cons]
          have inner : (Comp.letE term body).head =
              .free (request.outerLet body) := by
            simp [Comp.head, head]
          simpa [Frame.plug, FreeRequest.outerLet, List.append_assoc] using ih inner

@[simp] theorem BaseRequest.source_head (request : BaseRequest) :
    request.source.head = .base request := by
  cases request with
  | mk operation parameter context =>
      simpa [BaseRequest.source] using
        EvalContext.plug_head_base context
          (term := Comp.baseOp operation parameter)
          (request := BaseRequest.mk operation parameter []) rfl

@[simp] theorem FreeRequest.source_head (request : FreeRequest) :
    request.source.head = .free request := by
  cases request with
  | mk interface operation parameter context =>
      simpa [FreeRequest.source] using
        EvalContext.plug_head_free context
          (term := Comp.freeOp interface operation parameter)
          (request := FreeRequest.mk interface operation parameter []) rfl

@[simp] theorem Comp.observe_zero (term : Comp) : term.observe 0 = none := rfl

@[simp] theorem Comp.observe_return (fuel : Nat) (value : Val) :
    (Comp.ret value).observe (fuel + 1) = some (.returned value) := rfl

@[simp] theorem Comp.observe_base (fuel operation : Nat) (parameter : Val) :
    (Comp.baseOp operation parameter).observe (fuel + 1) =
      some (.base ⟨operation, parameter, []⟩) := rfl

@[simp] theorem Comp.observe_free (fuel interface operation : Nat)
    (parameter : Val) :
    (Comp.freeOp interface operation parameter).observe (fuel + 1) =
      some (.free ⟨interface, operation, parameter, []⟩) := rfl

/-- Once a finite observation appears, one extra unit of fuel preserves it. -/
theorem Comp.observe_succ_of_some
    {term : Comp} {fuel : Nat} {outcome : FiniteOutcome}
    (observed : term.observe fuel = some outcome) :
    term.observe (fuel + 1) = some outcome := by
  induction fuel generalizing term with
  | zero => simp [Comp.observe] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simpa [Comp.observe, found] using observed
      | internal next =>
          simp only [Comp.observe, found] at observed ⊢
          exact ih observed
      | base request => simpa [Comp.observe, found] using observed
      | free request => simpa [Comp.observe, found] using observed
      | stuck => simp [Comp.observe, found] at observed

theorem Comp.observe_mono
    {term : Comp} {fuel : Nat} {outcome : FiniteOutcome}
    (observed : term.observe fuel = some outcome) (extra : Nat) :
    term.observe (fuel + extra) = some outcome := by
  induction extra with
  | zero => simpa using observed
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Comp.observe_succ_of_some ih

@[simp] theorem silentLoop_head : silentLoop.head = .internal silentLoop := rfl

theorem silentLoop_unobservable (fuel : Nat) : silentLoop.observe fuel = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

/-- Finite convergence is existence of a successful finite observation. -/
def Comp.Converges (term : Comp) (outcome : FiniteOutcome) : Prop :=
  ∃ fuel, term.observe fuel = some outcome

theorem silentLoop_not_converges (outcome : FiniteOutcome) :
    ¬ silentLoop.Converges outcome := by
  rintro ⟨fuel, observed⟩
  rw [silentLoop_unobservable] at observed
  cases observed

/-- A partial finite-boundary denotation is a fuel-indexed observation that,
once defined, remains defined with the same result. -/
structure PartialObservation where
  observeAt : Nat → Option FiniteOutcome
  stable : ∀ {fuel outcome}, observeAt fuel = some outcome →
    observeAt (fuel + 1) = some outcome

def Comp.operationalApprox (term : Comp) : PartialObservation where
  observeAt fuel := term.observe fuel
  stable := Comp.observe_succ_of_some

def PartialObservation.bottom : PartialObservation where
  observeAt _ := none
  stable := by simp

instance : LE PartialObservation where
  le lower upper := ∀ fuel outcome,
    lower.observeAt fuel = some outcome →
      upper.observeAt fuel = some outcome

theorem PartialObservation.le_refl (observation : PartialObservation) :
    observation ≤ observation := by
  intro fuel outcome observed
  exact observed

theorem PartialObservation.le_trans {first second third : PartialObservation}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    first ≤ third := by
  intro fuel outcome observed
  exact secondThird fuel outcome (firstSecond fuel outcome observed)

theorem PartialObservation.bottom_le (observation : PartialObservation) :
    bottom ≤ observation := by
  intro fuel outcome observed
  simp [bottom] at observed

@[ext] theorem PartialObservation.ext
    {left right : PartialObservation}
    (equal : left.observeAt = right.observeAt) :
    left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem silentLoop_operationalApprox_bottom :
    silentLoop.operationalApprox = PartialObservation.bottom := by
  apply PartialObservation.ext
  funext fuel
  exact silentLoop_unobservable fuel

theorem return_operationalApprox_not_bottom (value : Val) :
    (Comp.ret value).operationalApprox ≠ PartialObservation.bottom := by
  intro equal
  have atOne := congrArg (fun observation => observation.observeAt 1) equal
  simp [Comp.operationalApprox, PartialObservation.bottom] at atOne

end EffectSemantics
