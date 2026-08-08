import EffectSemantics.Recursive.DeepExceptionBoundary

namespace EffectSemantics

inductive DeepStateBoundary where
  | returned (value : Val) (state : Bool)
  | base (request : BaseRequest) (state : Bool)
  | free (request : FreeRequest) (state : Bool)
  deriving DecidableEq

/-- Boolean State convention: operation zero is `get`, operation one is
`put`.  Other old-base operations remain outward boundaries. -/
def Comp.observeDeepStateBoundary : Nat → Nat → AffineHandler → Comp → Bool →
    Option DeepStateBoundary
  | 0, _, _, _, _ => none
  | fuel + 1, interface, handler, term, state =>
      match term.head with
      | .returned value => some (.returned value state)
      | .internal next =>
          next.observeDeepStateBoundary fuel interface handler state
      | .base request =>
          if request.operation = 0 then
            (request.resume (.bool state)).observeDeepStateBoundary
              fuel interface handler state
          else if request.operation = 1 then
            match request.parameter with
            | .bool newState =>
                (request.resume .unit).observeDeepStateBoundary
                  fuel interface handler newState
            | _ => none
          else some (.base request state)
      | .free request =>
          if request.interface = interface then
            match handler.lookup request.operation with
            | some clause =>
                (request.answerWith clause).observeDeepStateBoundary
                  fuel interface handler state
            | none => some (.free request state)
          else some (.free request state)
      | .stuck => none

theorem Comp.observeDeepStateBoundary_succ_of_some
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {state : Bool} {boundary : DeepStateBoundary}
    (observed : term.observeDeepStateBoundary fuel interface handler state =
      some boundary) :
    term.observeDeepStateBoundary (fuel + 1) interface handler state =
      some boundary := by
  induction fuel generalizing term state boundary with
  | zero => simp [Comp.observeDeepStateBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simpa [Comp.observeDeepStateBoundary, found] using observed
      | internal next =>
          simp only [Comp.observeDeepStateBoundary, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases isGet : request.operation = 0
          · simp only [Comp.observeDeepStateBoundary, found, isGet, if_pos]
              at observed ⊢
            exact ih observed
          · by_cases isPut : request.operation = 1
            · cases parameterFound : request.parameter <;>
                simp [Comp.observeDeepStateBoundary, found, isPut,
                  parameterFound] at observed ⊢
              exact ih observed
            · simpa [Comp.observeDeepStateBoundary, found, isGet, isPut]
                using observed
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simpa [Comp.observeDeepStateBoundary, found, same, clauseFound]
                  using observed
            | some clause =>
                simp only [Comp.observeDeepStateBoundary, found, same, if_pos,
                  clauseFound] at observed ⊢
                exact ih observed
          · simpa [Comp.observeDeepStateBoundary, found, same] using observed
      | stuck => simp [Comp.observeDeepStateBoundary, found] at observed

def Comp.deepStateBoundaryApprox (term : Comp) (interface : Nat)
    (handler : AffineHandler) (state : Bool) :
    StableObservation DeepStateBoundary where
  observeAt fuel := term.observeDeepStateBoundary fuel interface handler state
  stable := Comp.observeDeepStateBoundary_succ_of_some

noncomputable def Comp.deepStateBoundaryLimit (term : Comp) (interface : Nat)
    (handler : AffineHandler) (state : Bool) : Option DeepStateBoundary :=
  (term.deepStateBoundaryApprox interface handler state).limitOutcome

inductive DeepStateBoundaryRuns (interface : Nat) (handler : AffineHandler) :
    Comp → Bool → DeepStateBoundary → Prop where
  | returned : DeepStateBoundaryRuns interface handler (.ret value) state
      (.returned value state)
  | internal : Step term next →
      DeepStateBoundaryRuns interface handler next state boundary →
      DeepStateBoundaryRuns interface handler term state boundary
  | get : ExposesBase term request → request.operation = 0 →
      DeepStateBoundaryRuns interface handler
        (request.resume (.bool state)) state boundary →
      DeepStateBoundaryRuns interface handler term state boundary
  | put : ExposesBase term request → request.operation = 1 →
      request.parameter = .bool newState →
      DeepStateBoundaryRuns interface handler
        (request.resume .unit) newState boundary →
      DeepStateBoundaryRuns interface handler term state boundary
  | baseOut : ExposesBase term request → request.operation ≠ 0 →
      request.operation ≠ 1 →
      DeepStateBoundaryRuns interface handler term state (.base request state)
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      DeepStateBoundaryRuns interface handler
        (request.answerWith clause) state boundary →
      DeepStateBoundaryRuns interface handler term state boundary
  | freeOther : ExposesFree term request → request.interface ≠ interface →
      DeepStateBoundaryRuns interface handler term state (.free request state)
  | freeMissing : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = none →
      DeepStateBoundaryRuns interface handler term state (.free request state)

theorem DeepStateBoundaryRuns.to_observation
    (runs : DeepStateBoundaryRuns interface handler term state boundary) :
    ∃ fuel, term.observeDeepStateBoundary fuel interface handler state =
      some boundary := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by simp [Comp.observeDeepStateBoundary,
        step.to_head, observed]⟩
  | get exposed selected runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        BaseRequest.source_head, selected, observed]⟩
  | put exposed selected parameter runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        BaseRequest.source_head, selected, parameter, observed]⟩
  | baseOut exposed notGet notPut =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        BaseRequest.source_head, notGet, notPut]⟩
  | matched exposed same found runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        FreeRequest.source_head, same, found, observed]⟩
  | freeOther exposed different =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        FreeRequest.source_head, different]⟩
  | freeMissing exposed same missing =>
      exact ⟨1, by rw [exposed]; simp [Comp.observeDeepStateBoundary,
        FreeRequest.source_head, same, missing]⟩

theorem Comp.observeDeepStateBoundary_reflects
    (observed : term.observeDeepStateBoundary fuel interface handler state =
      some boundary) :
    DeepStateBoundaryRuns interface handler term state boundary := by
  induction fuel generalizing term state boundary with
  | zero => simp [Comp.observeDeepStateBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepStateBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [Comp.observeDeepStateBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases isGet : request.operation = 0
          · simp only [Comp.observeDeepStateBoundary, found, isGet, if_pos]
              at observed
            exact .get (Comp.head_base_sound found) isGet (ih observed)
          · by_cases isPut : request.operation = 1
            · cases parameterFound : request.parameter with
              | bool newState =>
                  simp [Comp.observeDeepStateBoundary, found, isPut,
                    parameterFound] at observed
                  exact .put (Comp.head_base_sound found) isPut parameterFound
                    (ih observed)
              | _ => simp [Comp.observeDeepStateBoundary, found, isPut,
                  parameterFound] at observed
            · simp [Comp.observeDeepStateBoundary, found, isGet, isPut] at observed
              subst boundary
              exact .baseOut (Comp.head_base_sound found) isGet isPut
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepStateBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact .matched (Comp.head_free_sound found) same clauseFound
                  (ih observed)
            | none =>
                simp [Comp.observeDeepStateBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .freeMissing (Comp.head_free_sound found) same clauseFound
          · simp [Comp.observeDeepStateBoundary, found, same] at observed
            subst boundary
            exact .freeOther (Comp.head_free_sound found) same
      | stuck => simp [Comp.observeDeepStateBoundary, found] at observed

theorem deep_state_boundary_limit_adequacy :
    DeepStateBoundaryRuns interface handler term state boundary ↔
      term.deepStateBoundaryLimit interface handler state = some boundary := by
  constructor
  · intro runs
    obtain ⟨fuel, observed⟩ := runs.to_observation
    exact StableObservation.limitOutcome_of_observed _ observed
  · intro observed
    obtain ⟨fuel, finite⟩ :=
      StableObservation.limitOutcome_some_witness _ observed
    exact Comp.observeDeepStateBoundary_reflects finite

theorem deep_state_boundary_runs_deterministic
    (first : DeepStateBoundaryRuns interface handler term state left)
    (second : DeepStateBoundaryRuns interface handler term state right) :
    left = right := by
  have leftObserved := deep_state_boundary_limit_adequacy.mp first
  have rightObserved := deep_state_boundary_limit_adequacy.mp second
  rw [leftObserved] at rightObserved
  exact Option.some.inj rightObserved

structure StateResponseLaws (sig : Signature) : Prop where
  getResponse : ∀ parameterTy responseTy,
    sig.base 0 = some ⟨parameterTy, responseTy⟩ → responseTy = .bool
  putResponse : ∀ parameterTy responseTy,
    sig.base 1 = some ⟨parameterTy, responseTy⟩ → responseTy = .unit

theorem DeepStateBoundaryRuns.dischargesAux
    (runs : DeepStateBoundaryRuns interface handler term state boundary)
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (stateLaws : StateResponseLaws sig)
    (boundaryEq : boundary = .free request finalState) :
    request.interface ≠ interface := by
  induction runs generalizing effect request finalState with
  | returned => cases boundaryEq
  | internal step runs ih => exact ih (step.preserve typing) boundaryEq
  | get exposed selected runs ih =>
      rename_i exposedTerm currentState currentBoundary
      rw [exposed] at typing
      let requestTyping := typing.exposedBaseView
      have responseEq : requestTyping.responseTy = .bool := by
        apply stateLaws.getResponse requestTyping.parameterTy
          requestTyping.responseTy
        simpa [selected] using requestTyping.lookup
      have responseTyping : HasVal sig [] (.bool currentState)
          requestTyping.responseTy := by
        rw [responseEq]
        exact .bool
      exact ih (requestTyping.resumeTyping responseTyping) boundaryEq
  | put exposed selected parameter runs ih =>
      rw [exposed] at typing
      let requestTyping := typing.exposedBaseView
      have responseEq : requestTyping.responseTy = .unit := by
        apply stateLaws.putResponse requestTyping.parameterTy
          requestTyping.responseTy
        simpa [selected] using requestTyping.lookup
      have responseTyping : HasVal sig [] .unit requestTyping.responseTy := by
        rw [responseEq]
        exact .unit
      exact ih (requestTyping.resumeTyping responseTyping) boundaryEq
  | baseOut => cases boundaryEq
  | matched exposed same found runs ih =>
      rw [exposed] at typing
      exact ih (handlerTyping.answerWithTyping typing same found) boundaryEq
  | freeOther exposed different =>
      rename_i exposedTerm exposedRequest currentState
      have equal := DeepStateBoundary.free.inj boundaryEq
      exact equal.1 ▸ different
  | freeMissing exposed same missing =>
      rename_i exposedTerm exposedRequest currentState
      rw [exposed] at typing
      let requestTyping := typing.exposedFreeView
      obtain ⟨clause, clauseFound⟩ := exhaustive exposedRequest.operation
        requestTyping.parameterTy requestTyping.responseTy (by
          simpa [same] using requestTyping.lookup)
      rw [missing] at clauseFound
      cases clauseFound

theorem deep_state_boundary_limit_discharges
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (stateLaws : StateResponseLaws sig)
    (observed : term.deepStateBoundaryLimit interface handler state =
      some (.free request finalState)) :
    request.interface ≠ interface :=
  (deep_state_boundary_limit_adequacy.mpr observed).dischargesAux
    typing handlerTyping exhaustive stateLaws rfl

end EffectSemantics
