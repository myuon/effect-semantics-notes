import EffectSemantics.Examples.GenericBaseInstances
import EffectSemantics.Recursive.GenericResumption

namespace EffectSemantics

/-!
# Generic recursive State observation

Unlike Writer and Exception, one finite State layer denotes a state
transformer.  Keeping this transformer in the outcome avoids pretending that
state can be folded without an initial store.
-/

abbrev GenericStateOutcome (Result : Type) :=
  Bool → Option (Result × Bool)

def observeGenericState
    (leaf : Leaf → Option (GenericStateOutcome Result)) :
    FreeExtension stateBaseSignature userOperationSignature Leaf →
      Option (GenericStateOutcome Result)
  | .ret value => leaf value
  | .baseOp .get continuation =>
      match observeGenericState leaf (continuation false),
          observeGenericState leaf (continuation true) with
      | some onFalse, some onTrue =>
          some (fun state => if state then onTrue true else onFalse false)
      | _, _ => none
  | .baseOp (.put nextState) continuation =>
      match observeGenericState leaf (continuation ()) with
      | some next => some (fun _ => next nextState)
      | none => none
  | .freeOp _operation _continuation => none

theorem observeGenericState_ret
    (leaf : Leaf → Option (GenericStateOutcome Result)) (value : Leaf) :
    observeGenericState leaf (.ret value) = leaf value := rfl

def genericRecursiveStateObserver (Result : Type) :
    RecursiveFiniteObserver stateBaseSignature userOperationSignature
      Result (GenericStateOutcome Result) where
  returned result := fun state => some (result, state)
  observe := observeGenericState
  observeRet := observeGenericState_ret

namespace GenericRecursiveState

abbrev Observer (Result : Type) := genericRecursiveStateObserver Result

theorem observe_mono
    {lower upper : Leaf → Option (GenericStateOutcome Result)}
    (bound : ∀ leaf outcome, lower leaf = some outcome →
      upper leaf = some outcome)
    (tree : FreeExtension stateBaseSignature userOperationSignature Leaf) :
    ∀ {outcome}, (Observer Result).observe lower tree = some outcome →
      (Observer Result).observe upper tree = some outcome := by
  induction tree with
  | ret value => exact fun {_} => bound value _
  | baseOp operation continuation ih =>
      cases operation with
      | get =>
          intro outcome observed
          simp only [Observer, genericRecursiveStateObserver,
            observeGenericState] at observed ⊢
          cases leftObserved : observeGenericState lower (continuation false) with
          | none =>
              rw [leftObserved] at observed
              contradiction
          | some left =>
              cases rightObserved : observeGenericState lower (continuation true) with
              | none => rw [leftObserved, rightObserved] at observed; contradiction
              | some right =>
                  have leftUpper := ih false (by
                    simpa [Observer, genericRecursiveStateObserver] using leftObserved)
                  have rightUpper := ih true (by
                    simpa [Observer, genericRecursiveStateObserver] using rightObserved)
                  simp only [Observer, genericRecursiveStateObserver] at leftUpper rightUpper
                  rw [leftObserved, rightObserved] at observed
                  rw [leftUpper, rightUpper]
                  exact observed
      | put nextState =>
          intro outcome observed
          simp only [Observer, genericRecursiveStateObserver,
            observeGenericState] at observed ⊢
          cases childObserved : observeGenericState lower (continuation ()) with
          | none => rw [childObserved] at observed; contradiction
          | some child =>
              have childUpper := ih () (by
                simpa [Observer, genericRecursiveStateObserver] using childObserved)
              simp only [Observer, genericRecursiveStateObserver] at childUpper
              rw [childObserved] at observed
              rw [childUpper]
              exact observed
  | freeOp operation continuation ih =>
      intro outcome observed
      simp [Observer, genericRecursiveStateObserver, observeGenericState] at observed

theorem leaf_observation_mono
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (bound : FlatApproximation.LE lower upper) :
    ∀ leaf outcome,
      RecursiveResumptionSystem.leafObservation observer lower leaf = some outcome →
      RecursiveResumptionSystem.leafObservation observer upper leaf = some outcome := by
  intro leaf outcome observed
  cases leaf with
  | inl result => exact observed
  | inr state => exact bound state outcome observed

theorem observe_sup_witness
    (chain : FlatApproximation.Chain State (GenericStateOutcome Result))
    (tree : FreeExtension stateBaseSignature userOperationSignature
      (Result ⊕ State)) (outcome)
    (observed : (Observer Result).observe
      (RecursiveResumptionSystem.leafObservation (Observer Result) chain.sup)
      tree = some outcome) :
    ∃ index, (Observer Result).observe
      (RecursiveResumptionSystem.leafObservation
        (Observer Result) (chain.sequence index)) tree = some outcome := by
  induction tree generalizing outcome with
  | ret leaf =>
      cases leaf with
      | inl result => exact ⟨0, observed⟩
      | inr state =>
          simp only [Observer, genericRecursiveStateObserver] at observed ⊢
          exact chain.sup_some_witness observed
  | baseOp operation continuation ih =>
      cases operation with
      | get =>
          simp only [Observer, genericRecursiveStateObserver,
            observeGenericState] at observed
          cases leftObserved : observeGenericState
              (RecursiveResumptionSystem.leafObservation
                (genericRecursiveStateObserver Result) chain.sup)
              (continuation false) with
          | none =>
              simp only [genericRecursiveStateObserver] at leftObserved
              rw [leftObserved] at observed
              contradiction
          | some left =>
              cases rightObserved : observeGenericState
                  (RecursiveResumptionSystem.leafObservation
                    (genericRecursiveStateObserver Result) chain.sup)
                  (continuation true) with
              | none =>
                  simp only [genericRecursiveStateObserver] at leftObserved rightObserved
                  rw [leftObserved, rightObserved] at observed
                  contradiction
              | some right =>
                  simp only [genericRecursiveStateObserver] at leftObserved rightObserved
                  obtain ⟨leftIndex, leftFinite⟩ := ih false left leftObserved
                  obtain ⟨rightIndex, rightFinite⟩ := ih true right rightObserved
                  let index := max leftIndex rightIndex
                  have leftBound : FlatApproximation.LE
                      (chain.sequence leftIndex) (chain.sequence index) :=
                    chain.mono (by
                      dsimp [index]
                      exact Nat.le_max_left _ _)
                  have rightBound : FlatApproximation.LE
                      (chain.sequence rightIndex) (chain.sequence index) :=
                    chain.mono (by
                      dsimp [index]
                      exact Nat.le_max_right _ _)
                  have leftAtIndex := observe_mono
                    (leaf_observation_mono (Observer Result) leftBound)
                    (continuation false) leftFinite
                  have rightAtIndex := observe_mono
                    (leaf_observation_mono (Observer Result) rightBound)
                    (continuation true) rightFinite
                  refine ⟨index, ?_⟩
                  simp only [Observer, genericRecursiveStateObserver,
                    observeGenericState]
                  simp only [Observer, genericRecursiveStateObserver] at leftAtIndex rightAtIndex
                  rw [leftAtIndex, rightAtIndex]
                  rw [leftObserved, rightObserved] at observed
                  exact observed
      | put nextState =>
          simp only [Observer, genericRecursiveStateObserver,
            observeGenericState] at observed
          cases childObserved : observeGenericState
              (RecursiveResumptionSystem.leafObservation
                (genericRecursiveStateObserver Result) chain.sup)
              (continuation ()) with
          | none =>
              simp only [genericRecursiveStateObserver] at childObserved
              rw [childObserved] at observed
              contradiction
          | some child =>
              simp only [genericRecursiveStateObserver] at childObserved
              obtain ⟨index, finite⟩ := ih () child childObserved
              refine ⟨index, ?_⟩
              simp only [Observer, genericRecursiveStateObserver,
                observeGenericState]
              simp only [Observer, genericRecursiveStateObserver] at finite
              rw [finite]
              rw [childObserved] at observed
              exact observed
  | freeOp operation continuation ih =>
      simp [Observer, genericRecursiveStateObserver, observeGenericState] at observed

theorem continuity : RecursiveObserverContinuity (Observer Result) where
  observeMono := fun bound tree _outcome observed =>
    observe_mono bound tree observed
  observeSupWitness := fun chain tree outcome =>
    observe_sup_witness chain tree outcome

theorem functional_continuous
    (system : RecursiveResumptionSystem
      stateBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      stateBaseSignature userOperationSignature) :
    FlatApproximation.OmegaContinuous
      (system.functional (Observer Result) handler) :=
  (continuity (Result := Result)).functionalContinuous
    (Observer Result) system handler

def cert
    (system : RecursiveResumptionSystem
      stateBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      stateBaseSignature userOperationSignature) :
    GenericRecursiveResumptionCert system (Observer Result) handler where
  continuous := functional_continuous system handler
  Runs := GenericRuns system (Observer Result) handler
  finiteAdequacy := genericFiniteAdequacy system (Observer Result) handler
  pole := fun _ _ => True
  layerPreservesPole := fun _ _ _ _ _ => trivial

theorem limit_adequacy
    (system : RecursiveResumptionSystem
      stateBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      stateBaseSignature userOperationSignature) :
    GenericRuns system (Observer Result) handler state outcome ↔
      (cert system handler).semantics state = some outcome :=
  (cert system handler).main.2.2.1

/-- A finite program that reads the store, negates it, and returns the old
store. -/
def toggleTree : FreeExtension stateBaseSignature userOperationSignature Bool :=
  .baseOp .get (fun old =>
    .baseOp (.put (!old)) (fun _ => .ret old))

theorem toggle_from_false :
    (Observer Bool).observe
        (fun result => some (fun state => some (result, state))) toggleTree =
      some transformer →
    transformer false = some (false, true) := by
  intro observed
  have equal : transformer = fun state =>
      if state then some (true, false) else some (false, true) :=
    Option.some.inj observed.symm
  rw [equal]
  rfl

theorem toggle_from_true :
    (Observer Bool).observe
        (fun result => some (fun state => some (result, state))) toggleTree =
      some transformer →
    transformer true = some (true, false) := by
  intro observed
  have equal : transformer = fun state =>
      if state then some (true, false) else some (false, true) :=
    Option.some.inj observed.symm
  rw [equal]
  rfl

end GenericRecursiveState
end EffectSemantics
