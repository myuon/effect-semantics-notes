import EffectSemantics.Recursive.DeepWriterBoundaryAdequacy

namespace EffectSemantics

inductive DeepExceptionBoundary where
  | returned (value : Val)
  | raised (error : Val)
  | base (request : BaseRequest)
  | free (request : FreeRequest)
  deriving DecidableEq

/-- Operation zero is the abortive `raise`; unlike Writer it never resumes. -/
def Comp.observeDeepExceptionBoundary : Nat → Nat → AffineHandler → Comp →
    Option DeepExceptionBoundary
  | 0, _, _, _ => none
  | fuel + 1, interface, handler, term =>
      match term.head with
      | .returned value => some (.returned value)
      | .internal next => next.observeDeepExceptionBoundary fuel interface handler
      | .base request =>
          if request.operation = 0 then some (.raised request.parameter)
          else some (.base request)
      | .free request =>
          if request.interface = interface then
            match handler.lookup request.operation with
            | some clause =>
                (request.answerWith clause).observeDeepExceptionBoundary
                  fuel interface handler
            | none => some (.free request)
          else some (.free request)
      | .stuck => none

theorem Comp.observeDeepExceptionBoundary_succ_of_some
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {boundary : DeepExceptionBoundary}
    (observed : term.observeDeepExceptionBoundary fuel interface handler =
      some boundary) :
    term.observeDeepExceptionBoundary (fuel + 1) interface handler =
      some boundary := by
  induction fuel generalizing term boundary with
  | zero => simp [Comp.observeDeepExceptionBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simpa [Comp.observeDeepExceptionBoundary, found] using observed
      | internal next =>
          simp only [Comp.observeDeepExceptionBoundary, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases raised : request.operation = 0 <;>
            simpa [Comp.observeDeepExceptionBoundary, found, raised] using observed
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simpa [Comp.observeDeepExceptionBoundary, found, same, clauseFound]
                  using observed
            | some clause =>
                simp only [Comp.observeDeepExceptionBoundary, found, same, if_pos,
                  clauseFound] at observed ⊢
                exact ih observed
          · simpa [Comp.observeDeepExceptionBoundary, found, same] using observed
      | stuck => simp [Comp.observeDeepExceptionBoundary, found] at observed

def Comp.deepExceptionBoundaryApprox (term : Comp) (interface : Nat)
    (handler : AffineHandler) : StableObservation DeepExceptionBoundary where
  observeAt fuel := term.observeDeepExceptionBoundary fuel interface handler
  stable := Comp.observeDeepExceptionBoundary_succ_of_some

noncomputable def Comp.deepExceptionBoundaryLimit (term : Comp)
    (interface : Nat) (handler : AffineHandler) : Option DeepExceptionBoundary :=
  (term.deepExceptionBoundaryApprox interface handler).limitOutcome

inductive DeepExceptionBoundaryRuns (interface : Nat) (handler : AffineHandler) :
    Comp → DeepExceptionBoundary → Prop where
  | returned : DeepExceptionBoundaryRuns interface handler (.ret value)
      (.returned value)
  | internal : Step term next →
      DeepExceptionBoundaryRuns interface handler next boundary →
      DeepExceptionBoundaryRuns interface handler term boundary
  | raised : ExposesBase term request → request.operation = 0 →
      DeepExceptionBoundaryRuns interface handler term (.raised request.parameter)
  | baseOut : ExposesBase term request → request.operation ≠ 0 →
      DeepExceptionBoundaryRuns interface handler term (.base request)
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      DeepExceptionBoundaryRuns interface handler (request.answerWith clause) boundary →
      DeepExceptionBoundaryRuns interface handler term boundary
  | freeOther : ExposesFree term request → request.interface ≠ interface →
      DeepExceptionBoundaryRuns interface handler term (.free request)
  | freeMissing : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = none →
      DeepExceptionBoundaryRuns interface handler term (.free request)

theorem DeepExceptionBoundaryRuns.to_observation
    (runs : DeepExceptionBoundaryRuns interface handler term boundary) :
    ∃ fuel, term.observeDeepExceptionBoundary fuel interface handler =
      some boundary := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by
        simp [Comp.observeDeepExceptionBoundary, step.to_head, observed]⟩
  | raised exposed selected =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepExceptionBoundary,
        BaseRequest.source_head, selected]⟩
  | baseOut exposed different =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepExceptionBoundary,
        BaseRequest.source_head, different]⟩
  | matched exposed same found runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by rw [exposed]; simp [Comp.observeDeepExceptionBoundary,
        FreeRequest.source_head, same, found, observed]⟩
  | freeOther exposed different =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepExceptionBoundary,
        FreeRequest.source_head, different]⟩
  | freeMissing exposed same missing =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepExceptionBoundary,
        FreeRequest.source_head, same, missing]⟩

theorem Comp.observeDeepExceptionBoundary_reflects
    (observed : term.observeDeepExceptionBoundary fuel interface handler =
      some boundary) :
    DeepExceptionBoundaryRuns interface handler term boundary := by
  induction fuel generalizing term boundary with
  | zero => simp [Comp.observeDeepExceptionBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepExceptionBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [Comp.observeDeepExceptionBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases raised : request.operation = 0
          · simp [Comp.observeDeepExceptionBoundary, found, raised] at observed
            subst boundary
            exact .raised (Comp.head_base_sound found) raised
          · simp [Comp.observeDeepExceptionBoundary, found, raised] at observed
            subst boundary
            exact .baseOut (Comp.head_base_sound found) raised
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepExceptionBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact .matched (Comp.head_free_sound found) same clauseFound
                  (ih observed)
            | none =>
                simp [Comp.observeDeepExceptionBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .freeMissing (Comp.head_free_sound found) same clauseFound
          · simp [Comp.observeDeepExceptionBoundary, found, same] at observed
            subst boundary
            exact .freeOther (Comp.head_free_sound found) same
      | stuck => simp [Comp.observeDeepExceptionBoundary, found] at observed

theorem deep_exception_boundary_limit_adequacy :
    DeepExceptionBoundaryRuns interface handler term boundary ↔
      term.deepExceptionBoundaryLimit interface handler = some boundary := by
  constructor
  · intro runs
    obtain ⟨fuel, observed⟩ := runs.to_observation
    exact StableObservation.limitOutcome_of_observed _ observed
  · intro observed
    obtain ⟨fuel, finite⟩ :=
      StableObservation.limitOutcome_some_witness _ observed
    exact Comp.observeDeepExceptionBoundary_reflects finite

theorem deep_exception_boundary_runs_deterministic
    (first : DeepExceptionBoundaryRuns interface handler term left)
    (second : DeepExceptionBoundaryRuns interface handler term right) :
    left = right := by
  have leftObserved := deep_exception_boundary_limit_adequacy.mp first
  have rightObserved := deep_exception_boundary_limit_adequacy.mp second
  rw [leftObserved] at rightObserved
  exact Option.some.inj rightObserved

theorem DeepExceptionBoundaryRuns.dischargesAux
    (runs : DeepExceptionBoundaryRuns interface handler term boundary)
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (boundaryEq : boundary = .free request) :
    request.interface ≠ interface := by
  induction runs generalizing effect request with
  | returned => cases boundaryEq
  | internal step runs ih => exact ih (step.preserve typing) boundaryEq
  | raised => cases boundaryEq
  | baseOut => cases boundaryEq
  | matched exposed same found runs ih =>
      rw [exposed] at typing
      exact ih (handlerTyping.answerWithTyping typing same found) boundaryEq
  | freeOther exposed different =>
      rename_i exposedTerm exposedRequest
      have requestEq := DeepExceptionBoundary.free.inj boundaryEq
      exact requestEq ▸ different
  | freeMissing exposed same missing =>
      rename_i exposedTerm exposedRequest
      have requestEq := DeepExceptionBoundary.free.inj boundaryEq
      rw [exposed] at typing
      let requestTyping := typing.exposedFreeView
      obtain ⟨clause, clauseFound⟩ := exhaustive exposedRequest.operation
        requestTyping.parameterTy requestTyping.responseTy (by
          simpa [same] using requestTyping.lookup)
      rw [missing] at clauseFound
      cases clauseFound

theorem DeepExceptionBoundaryRuns.discharges
    (runs : DeepExceptionBoundaryRuns interface handler term (.free request))
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface) :
    request.interface ≠ interface :=
  runs.dischargesAux typing handlerTyping exhaustive rfl

theorem deep_exception_boundary_limit_discharges
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (observed : term.deepExceptionBoundaryLimit interface handler =
      some (.free request)) :
    request.interface ≠ interface :=
  (deep_exception_boundary_limit_adequacy.mpr observed).discharges
    typing handlerTyping exhaustive

end EffectSemantics
