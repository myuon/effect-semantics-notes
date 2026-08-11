import EffectSemantics.Theory.RecursiveModels

namespace EffectSemantics

inductive TypedDeepExceptionBoundary (sig : Signature) (resultTy : Ty) :
    DeepExceptionBoundary → Prop where
  | returned : Nonempty (HasVal sig [] value resultTy) →
      TypedDeepExceptionBoundary sig resultTy (.returned value)
  | raised : (∃ errorTy, Nonempty (HasVal sig [] error errorTy)) →
      TypedDeepExceptionBoundary sig resultTy (.raised error)
  | base : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepExceptionBoundary sig resultTy (.base request)
  | free : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepExceptionBoundary sig resultTy (.free request)

theorem observeDeepExceptionBoundary_typed
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (observed : term.observeDeepExceptionBoundary fuel interface handler =
      some boundary) :
    TypedDeepExceptionBoundary sig resultTy boundary := by
  induction fuel generalizing term effect boundary with
  | zero => simp [Comp.observeDeepExceptionBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepExceptionBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned ⟨typing.returnView.valueTyping⟩
      | internal next =>
          simp only [Comp.observeDeepExceptionBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact ih (step.preserve typing) observed
      | base request =>
          have exposed := Comp.head_base_sound found
          rw [exposed] at typing
          by_cases raised : request.operation = 0
          · simp [Comp.observeDeepExceptionBoundary, found, raised] at observed
            subst boundary
            let requestTyping := typing.exposedBaseView
            exact .raised ⟨requestTyping.parameterTy,
              ⟨requestTyping.parameterTyping⟩⟩
          · simp [Comp.observeDeepExceptionBoundary, found, raised] at observed
            subst boundary
            exact .base ⟨typing⟩
      | free request =>
          have exposed := Comp.head_free_sound found
          rw [exposed] at typing
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepExceptionBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact ih (handlerTyping.answerWithTyping typing same clauseFound)
                  observed
            | none =>
                simp [Comp.observeDeepExceptionBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .free ⟨typing⟩
          · simp [Comp.observeDeepExceptionBoundary, found, same] at observed
            subst boundary
            exact .free ⟨typing⟩
      | stuck => simp [Comp.observeDeepExceptionBoundary, found] at observed

theorem recursive_exception_fundamental
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (observed : term.deepExceptionBoundaryLimit interface handler =
      some boundary) :
    TypedDeepExceptionBoundary sig resultTy boundary := by
  obtain ⟨fuel, finite⟩ :=
    StableObservation.limitOutcome_some_witness _ observed
  exact observeDeepExceptionBoundary_typed typing handlerTyping finite

def RecursiveExceptionComputationRelation (sig : Signature) (resultTy : Ty)
    (interface : Nat) (handler : AffineHandler) (term : Comp) : Prop :=
  ∀ boundary, term.deepExceptionBoundaryLimit interface handler = some boundary →
    TypedDeepExceptionBoundary sig resultTy boundary

theorem recursive_exception_fundamental_open
    (typing : HasComp sig ctx term resultTy effect)
    (environment : RecursiveEnvironmentRelation sig ctx substitution)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect) :
    RecursiveExceptionComputationRelation sig resultTy interface handler
      (term.subst substitution) := by
  obtain ⟨preserves⟩ := environment
  intro boundary observed
  exact recursive_exception_fundamental
    (typing.subst_preserved preserves) handlerTyping observed

theorem recursive_exception_typed_pole_admissible :
    StableObservation.Admissible
      (StableObservation.Satisfies
        (TypedDeepExceptionBoundary sig resultTy)) :=
  StableObservation.satisfies_admissible _

inductive TypedDeepStateBoundary (sig : Signature) (resultTy : Ty) :
    DeepStateBoundary → Prop where
  | returned : Nonempty (HasVal sig [] value resultTy) →
      TypedDeepStateBoundary sig resultTy (.returned value state)
  | base : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepStateBoundary sig resultTy (.base request state)
  | free : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepStateBoundary sig resultTy (.free request state)

theorem observeDeepStateBoundary_typed
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (stateLaws : StateResponseLaws sig)
    (observed : term.observeDeepStateBoundary fuel interface handler state =
      some boundary) :
    TypedDeepStateBoundary sig resultTy boundary := by
  induction fuel generalizing term effect state boundary with
  | zero => simp [Comp.observeDeepStateBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepStateBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned ⟨typing.returnView.valueTyping⟩
      | internal next =>
          simp only [Comp.observeDeepStateBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact ih (step.preserve typing) observed
      | base request =>
          have exposed := Comp.head_base_sound found
          rw [exposed] at typing
          let requestTyping := typing.exposedBaseView
          by_cases isGet : request.operation = 0
          · simp only [Comp.observeDeepStateBoundary, found, isGet, if_pos]
              at observed
            have responseEq : requestTyping.responseTy = .bool := by
              apply stateLaws.getResponse requestTyping.parameterTy
                requestTyping.responseTy
              simpa [isGet] using requestTyping.lookup
            have responseTyping : HasVal sig [] (.bool state)
                requestTyping.responseTy := by
              rw [responseEq]
              exact .bool
            exact ih (requestTyping.resumeTyping responseTyping) observed
          · by_cases isPut : request.operation = 1
            · cases parameterFound : request.parameter with
              | bool newState =>
                  simp [Comp.observeDeepStateBoundary, found, isPut,
                    parameterFound] at observed
                  have responseEq : requestTyping.responseTy = .unit := by
                    apply stateLaws.putResponse requestTyping.parameterTy
                      requestTyping.responseTy
                    simpa [isPut] using requestTyping.lookup
                  have responseTyping : HasVal sig [] .unit
                      requestTyping.responseTy := by
                    rw [responseEq]
                    exact .unit
                  exact ih (requestTyping.resumeTyping responseTyping)
                    observed
              | _ => simp [Comp.observeDeepStateBoundary, found, isPut,
                  parameterFound] at observed
            · simp [Comp.observeDeepStateBoundary, found, isGet, isPut] at observed
              subst boundary
              exact .base ⟨typing⟩
      | free request =>
          have exposed := Comp.head_free_sound found
          rw [exposed] at typing
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepStateBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact ih (handlerTyping.answerWithTyping typing same clauseFound)
                  observed
            | none =>
                simp [Comp.observeDeepStateBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .free ⟨typing⟩
          · simp [Comp.observeDeepStateBoundary, found, same] at observed
            subst boundary
            exact .free ⟨typing⟩
      | stuck => simp [Comp.observeDeepStateBoundary, found] at observed

theorem recursive_state_fundamental
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (stateLaws : StateResponseLaws sig)
    (observed : term.deepStateBoundaryLimit interface handler state =
      some boundary) :
    TypedDeepStateBoundary sig resultTy boundary := by
  obtain ⟨fuel, finite⟩ :=
    StableObservation.limitOutcome_some_witness _ observed
  exact observeDeepStateBoundary_typed typing handlerTyping stateLaws finite

def RecursiveStateComputationRelation (sig : Signature) (resultTy : Ty)
    (interface : Nat) (handler : AffineHandler) (state : Bool)
    (term : Comp) : Prop :=
  ∀ boundary, term.deepStateBoundaryLimit interface handler state = some boundary →
    TypedDeepStateBoundary sig resultTy boundary

theorem recursive_state_fundamental_open
    (typing : HasComp sig ctx term resultTy effect)
    (environment : RecursiveEnvironmentRelation sig ctx substitution)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (stateLaws : StateResponseLaws sig) :
    RecursiveStateComputationRelation sig resultTy interface handler state
      (term.subst substitution) := by
  obtain ⟨preserves⟩ := environment
  intro boundary observed
  exact recursive_state_fundamental (typing.subst_preserved preserves)
    handlerTyping stateLaws observed

theorem recursive_state_typed_pole_admissible :
    StableObservation.Admissible
      (StableObservation.Satisfies
        (TypedDeepStateBoundary sig resultTy)) :=
  StableObservation.satisfies_admissible _

end EffectSemantics
