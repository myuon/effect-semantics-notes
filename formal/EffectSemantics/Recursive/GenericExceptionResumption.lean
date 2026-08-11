import EffectSemantics.Examples.GenericBaseInstances
import EffectSemantics.Recursive.GenericResumption

namespace EffectSemantics

/-!
# Generic recursive Exception instance

Exceptions terminate the current finite layer, while an unhandled newly
adjoined operation remains unobservable.
-/

def observeGenericException (leaf : Leaf → Option (Except Val Result)) :
    FreeExtension exceptionBaseSignature userOperationSignature Leaf →
      Option (Except Val Result)
  | .ret value => leaf value
  | .baseOp (.raise error) _continuation => some (.error error)
  | .freeOp _operation _continuation => none

theorem observeGenericException_ret
    (leaf : Leaf → Option (Except Val Result)) (value : Leaf) :
    observeGenericException leaf (.ret value) = leaf value := rfl

def genericRecursiveExceptionObserver (Result : Type) :
    RecursiveFiniteObserver exceptionBaseSignature userOperationSignature
      Result (Except Val Result) where
  returned := Except.ok
  observe := observeGenericException
  observeRet := observeGenericException_ret

namespace GenericRecursiveException

abbrev Observer (Result : Type) := genericRecursiveExceptionObserver Result

theorem observe_mono
    {lower upper : Leaf → Option (Except Val Result)}
    (bound : ∀ leaf outcome, lower leaf = some outcome →
      upper leaf = some outcome)
    (tree : FreeExtension exceptionBaseSignature userOperationSignature Leaf) :
    ∀ outcome, (Observer Result).observe lower tree = some outcome →
      (Observer Result).observe upper tree = some outcome := by
  induction tree with
  | ret value => exact fun outcome => bound value outcome
  | baseOp operation continuation ih =>
      cases operation with
      | raise error => intro outcome observed; exact observed
  | freeOp operation continuation ih =>
      intro outcome observed
      simp [Observer, genericRecursiveExceptionObserver,
        observeGenericException] at observed

theorem observe_sup_witness
    (chain : FlatApproximation.Chain State (Except Val Result))
    (tree : FreeExtension exceptionBaseSignature userOperationSignature
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
          simp only [Observer, genericRecursiveExceptionObserver] at observed ⊢
          exact chain.sup_some_witness observed
  | baseOp operation continuation ih =>
      cases operation with
      | raise error => exact ⟨0, observed⟩
  | freeOp operation continuation ih =>
      simp [Observer, genericRecursiveExceptionObserver,
        observeGenericException] at observed

theorem continuity : RecursiveObserverContinuity (Observer Result) where
  observeMono := fun bound tree outcome => observe_mono bound tree outcome
  observeSupWitness := fun chain tree outcome =>
    observe_sup_witness chain tree outcome

theorem functional_continuous
    (system : RecursiveResumptionSystem
      exceptionBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      exceptionBaseSignature userOperationSignature) :
    FlatApproximation.OmegaContinuous
      (system.functional (Observer Result) handler) :=
  (continuity (Result := Result)).functionalContinuous
    (Observer Result) system handler

def model
    (system : RecursiveResumptionSystem
      exceptionBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      exceptionBaseSignature userOperationSignature) :
    GenericRecursiveResumption system (Observer Result) handler where
  continuous := functional_continuous system handler
  Runs := GenericRuns system (Observer Result) handler
  finiteAdequacy := genericFiniteAdequacy system (Observer Result) handler
  pole := fun _ _ => True
  layerPreservesPole := fun _ _ _ _ _ => trivial

theorem limit_adequacy
    (system : RecursiveResumptionSystem
      exceptionBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      exceptionBaseSignature userOperationSignature) :
    GenericRuns system (Observer Result) handler state outcome ↔
      (model system handler).semantics state = some outcome :=
  (model system handler).main.2.2.1

end GenericRecursiveException
end EffectSemantics
