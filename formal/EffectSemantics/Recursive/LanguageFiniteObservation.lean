import EffectSemantics.Denotational.LanguageSourceShallow
import EffectSemantics.Recursive.StableObservation

namespace EffectSemantics

/-- Deterministic head classification for the language-graded source. -/
inductive LanguageHead where
  | returned (value : FinLanguageVal)
  | internal (next : FinLanguageComp)
  | base (request : LanguageBaseRequest)
  | free (request : LanguageFreeRequest)
  | stuck

def LanguageComp.head : FinLanguageComp → LanguageHead
  | .ret value => .returned value
  | .letE bound body =>
      match bound.head with
      | .returned value => .internal (body.subst0 value)
      | .internal next => .internal (.letE next body)
      | .base request => .base (request.outerLet body)
      | .free request => .free (request.outerLet body)
      | .stuck => .stuck
  | .app (.lam _ _ body) argument => .internal (body.subst0 argument)
  | .app (.fixLam allowed _ _ _) _ => nomatch allowed
  | .app _ _ => .stuck
  | .ite (.bool true) thenBranch _ => .internal thenBranch
  | .ite (.bool false) _ elseBranch => .internal elseBranch
  | .ite _ _ _ => .stuck
  | .case (.inl value _) leftBranch _ => .internal (leftBranch.subst0 value)
  | .case (.inr _ value) _ rightBranch => .internal (rightBranch.subst0 value)
  | .case _ _ _ => .stuck
  | .baseOp operation parameter => .base ⟨operation, parameter, []⟩
  | .freeOp interface operation parameter =>
      .free ⟨interface, operation, parameter, []⟩

theorem LanguageStep.to_head (step : term ⟶ next) :
    term.head = .internal next := by
  induction step with
  | letReturn => rfl
  | beta => rfl
  | fixBeta => nomatch ‹FixAllowed .finite›
  | ifTrue => rfl
  | ifFalse => rfl
  | caseInl => rfl
  | caseInr => rfl
  | underLet inner ih => simp [LanguageComp.head, ih]

theorem LanguageEvalContext.plug_head_base (context : LanguageEvalContext)
    (head : term.head = .base request) :
    (context.plug term).head = .base { request with
      context := request.context ++ context } := by
  induction context generalizing term request with
  | nil =>
      cases request
      simpa [LanguageEvalContext.plug] using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          have inner : (LanguageComp.letE term body).head =
              .base (request.outerLet body) := by
            simp [LanguageComp.head, head]
          simpa [LanguageEvalContext.plug, LanguageFrame.plug,
            LanguageBaseRequest.outerLet,
            List.append_assoc] using ih inner

theorem LanguageEvalContext.plug_head_free (context : LanguageEvalContext)
    (head : term.head = .free request) :
    (context.plug term).head = .free { request with
      context := request.context ++ context } := by
  induction context generalizing term request with
  | nil =>
      cases request
      simpa [LanguageEvalContext.plug] using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          have inner : (LanguageComp.letE term body).head =
              .free (request.outerLet body) := by
            simp [LanguageComp.head, head]
          simpa [LanguageEvalContext.plug, LanguageFrame.plug,
            LanguageFreeRequest.outerLet,
            List.append_assoc] using ih inner

@[simp] theorem LanguageBaseRequest.source_head (request : LanguageBaseRequest) :
    request.source.head = .base request := by
  cases request with
  | mk operation parameter context =>
      simpa [LanguageBaseRequest.source] using
        LanguageEvalContext.plug_head_base context
          (term := LanguageComp.baseOp operation parameter)
          (request := LanguageBaseRequest.mk operation parameter []) rfl

@[simp] theorem LanguageFreeRequest.source_head (request : LanguageFreeRequest) :
    request.source.head = .free request := by
  cases request with
  | mk interface operation parameter context =>
      simpa [LanguageFreeRequest.source] using
        LanguageEvalContext.plug_head_free context
          (term := LanguageComp.freeOp interface operation parameter)
          (request := LanguageFreeRequest.mk interface operation parameter []) rfl

mutual
  theorem LanguageComp.head_returned_sound
      {term : FinLanguageComp} {value : FinLanguageVal}
      (equal : term.head = LanguageHead.returned value) :
      term = LanguageComp.ret value := by
    cases term with
    | ret result => simp [LanguageComp.head] at equal; cases equal; rfl
    | letE bound body =>
        cases found : bound.head <;> simp [LanguageComp.head, found] at equal
    | app function argument =>
        cases function with
        | fixLam allowed _ _ _ => nomatch allowed
        | _ => simp [LanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [LanguageComp.head] at equal
        | _ => simp [LanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [LanguageComp.head] at equal
    | baseOp operation parameter => simp [LanguageComp.head] at equal
    | freeOp interface operation parameter => simp [LanguageComp.head] at equal

  theorem LanguageComp.head_internal_sound
      {term next : FinLanguageComp}
      (equal : term.head = .internal next) : Nonempty (term ⟶ next) := by
    cases term with
    | ret value => simp [LanguageComp.head] at equal
    | letE bound body =>
        cases found : bound.head with
        | returned value =>
            have source := LanguageComp.head_returned_sound found
            subst bound
            simp [LanguageComp.head] at equal
            subst next
            exact ⟨.letReturn⟩
        | internal inner =>
            simp [LanguageComp.head, found] at equal
            subst next
            obtain ⟨step⟩ := LanguageComp.head_internal_sound found
            exact ⟨.underLet step⟩
        | base request => simp [LanguageComp.head, found] at equal
        | free request => simp [LanguageComp.head, found] at equal
        | stuck => simp [LanguageComp.head, found] at equal
    | app function argument =>
        cases function with
        | lam domain latent body =>
            simp [LanguageComp.head] at equal
            subst next
            exact ⟨.beta⟩
        | fixLam allowed _ _ _ => nomatch allowed
        | _ => simp [LanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag =>
            cases flag <;> simp [LanguageComp.head] at equal
            · subst next; exact ⟨.ifFalse⟩
            · subst next; exact ⟨.ifTrue⟩
        | _ => simp [LanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [LanguageComp.head] at equal
        · subst next; exact ⟨.caseInl⟩
        · subst next; exact ⟨.caseInr⟩
    | baseOp operation parameter => simp [LanguageComp.head] at equal
    | freeOp interface operation parameter => simp [LanguageComp.head] at equal

  theorem LanguageComp.head_base_sound
      {term : FinLanguageComp} {request : LanguageBaseRequest}
      (equal : term.head = .base request) : term = request.source := by
    cases term with
    | ret value => simp [LanguageComp.head] at equal
    | letE bound body =>
        cases found : bound.head with
        | returned value => simp [LanguageComp.head, found] at equal
        | internal inner => simp [LanguageComp.head, found] at equal
        | base innerRequest =>
            simp [LanguageComp.head, found] at equal
            subst request
            have exposed := LanguageComp.head_base_sound found
            rw [exposed, LanguageBaseRequest.outerLet_source]
        | free innerRequest => simp [LanguageComp.head, found] at equal
        | stuck => simp [LanguageComp.head, found] at equal
    | app function argument =>
        cases function with
        | fixLam allowed _ _ _ => nomatch allowed
        | _ => simp [LanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [LanguageComp.head] at equal
        | _ => simp [LanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [LanguageComp.head] at equal
    | baseOp operation parameter =>
        simp [LanguageComp.head] at equal
        subst request
        rfl
    | freeOp interface operation parameter => simp [LanguageComp.head] at equal

  theorem LanguageComp.head_free_sound
      {term : FinLanguageComp} {request : LanguageFreeRequest}
      (equal : term.head = .free request) : term = request.source := by
    cases term with
    | ret value => simp [LanguageComp.head] at equal
    | letE bound body =>
        cases found : bound.head with
        | returned value => simp [LanguageComp.head, found] at equal
        | internal inner => simp [LanguageComp.head, found] at equal
        | base innerRequest => simp [LanguageComp.head, found] at equal
        | free innerRequest =>
            simp [LanguageComp.head, found] at equal
            subst request
            have exposed := LanguageComp.head_free_sound found
            rw [exposed, LanguageFreeRequest.outerLet_source]
        | stuck => simp [LanguageComp.head, found] at equal
    | app function argument =>
        cases function with
        | fixLam allowed _ _ _ => nomatch allowed
        | _ => simp [LanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [LanguageComp.head] at equal
        | _ => simp [LanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [LanguageComp.head] at equal
    | baseOp operation parameter => simp [LanguageComp.head] at equal
    | freeOp interface operation parameter =>
        simp [LanguageComp.head] at equal
        subst request
        rfl
end

inductive LanguageFiniteOutcome where
  | returned (value : FinLanguageVal)
  | base (request : LanguageBaseRequest)
  | free (request : LanguageFreeRequest)

/-- Fuel counts internal CBV reductions; a visible head is observed directly. -/
def LanguageComp.observe : Nat → FinLanguageComp → Option LanguageFiniteOutcome
  | 0, _ => none
  | fuel + 1, term =>
      match term.head with
      | .returned value => some (.returned value)
      | .internal next => next.observe fuel
      | .base request => some (.base request)
      | .free request => some (.free request)
      | .stuck => none

theorem LanguageComp.observe_succ_of_some
    {term : FinLanguageComp} {fuel : Nat} {outcome : LanguageFiniteOutcome}
    (observed : term.observe fuel = some outcome) :
    term.observe (fuel + 1) = some outcome := by
  induction fuel generalizing term with
  | zero => simp [LanguageComp.observe] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simpa [LanguageComp.observe, found] using observed
      | internal next =>
          simp only [LanguageComp.observe, found] at observed ⊢
          exact ih observed
      | base request => simpa [LanguageComp.observe, found] using observed
      | free request => simpa [LanguageComp.observe, found] using observed
      | stuck => simp [LanguageComp.observe, found] at observed

def LanguageComp.stableObservation (term : FinLanguageComp) :
    StableObservation LanguageFiniteOutcome where
  observeAt fuel := term.observe fuel
  stable := LanguageComp.observe_succ_of_some

end EffectSemantics
