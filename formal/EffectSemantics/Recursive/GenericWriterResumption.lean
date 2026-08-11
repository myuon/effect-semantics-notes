import EffectSemantics.Examples.GenericBaseInstances
import EffectSemantics.Recursive.GenericResumption

namespace EffectSemantics

/-!
# Generic recursive Writer instance

This module interprets base-independent resumptions with the concrete Writer
observation and proves continuity, finite-fuel adequacy, and limit adequacy.
-/

def observeGenericWriter (leaf : Leaf → Option (List Val × Result)) :
    FreeExtension writerBaseSignature userOperationSignature Leaf →
      Option (List Val × Result)
  | .ret value => leaf value
  | .baseOp (.tell message) continuation =>
      match observeGenericWriter leaf (continuation ()) with
      | none => none
      | some (log, result) => some (message :: log, result)
  | .freeOp _operation _continuation => none

theorem observeGenericWriter_ret
    (leaf : Leaf → Option (List Val × Result)) (value : Leaf) :
    observeGenericWriter leaf (.ret value) = leaf value := rfl

def genericRecursiveWriterObserver (Result : Type) :
    RecursiveFiniteObserver writerBaseSignature userOperationSignature
      Result (List Val × Result) where
  returned result := ([], result)
  observe := observeGenericWriter
  observeRet := observeGenericWriter_ret

namespace GenericRecursiveWriter

abbrev Observer (Result : Type) := genericRecursiveWriterObserver Result

theorem observe_mono
    {lower upper : Leaf → Option (List Val × Result)}
    (bound : ∀ leaf outcome, lower leaf = some outcome →
      upper leaf = some outcome)
    (tree : FreeExtension writerBaseSignature userOperationSignature Leaf) :
    ∀ {outcome}, (Observer Result).observe lower tree = some outcome →
      (Observer Result).observe upper tree = some outcome := by
  induction tree with
  | ret value => exact fun {_} => bound value _
  | baseOp operation continuation ih =>
      cases operation with
      | tell message =>
          intro outcome observed
          let response : writerBaseSignature.Response (.tell message) := ()
          simp only [Observer, genericRecursiveWriterObserver,
            observeGenericWriter] at observed ⊢
          cases lowerObserved : observeGenericWriter lower
              (continuation response) with
          | none => rw [lowerObserved] at observed; contradiction
          | some pair =>
              rcases pair with ⟨log, result⟩
              have upperObserved := ih response (by
                simpa [Observer, genericRecursiveWriterObserver] using lowerObserved)
              simp only [Observer, genericRecursiveWriterObserver] at upperObserved
              rw [lowerObserved] at observed
              rw [upperObserved]
              exact observed
  | freeOp operation continuation ih =>
      intro outcome observed
      simp [Observer, genericRecursiveWriterObserver, observeGenericWriter] at observed

theorem observe_sup_witness
    (chain : FlatApproximation.Chain State (List Val × Result))
    (tree : FreeExtension writerBaseSignature userOperationSignature
      (Result ⊕ State))
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
          simp only [Observer, genericRecursiveWriterObserver] at observed ⊢
          exact chain.sup_some_witness observed
  | baseOp operation continuation ih =>
      cases operation with
      | tell message =>
          let response : writerBaseSignature.Response (.tell message) := ()
          simp only [Observer, genericRecursiveWriterObserver,
            observeGenericWriter] at observed
          cases childObserved : observeGenericWriter
              (RecursiveResumptionSystem.leafObservation (Observer Result) chain.sup)
              (continuation response) with
          | none =>
              dsimp [response] at childObserved
              dsimp [RecursiveResumptionSystem.leafObservation, Observer,
                genericRecursiveWriterObserver] at observed childObserved
              rw [childObserved] at observed
              contradiction
          | some pair =>
              rcases pair with ⟨log, result⟩
              obtain ⟨index, finite⟩ := ih response (by
                simpa [Observer, genericRecursiveWriterObserver] using childObserved)
              refine ⟨index, ?_⟩
              simp only [Observer, genericRecursiveWriterObserver,
                observeGenericWriter]
              simp only [Observer, genericRecursiveWriterObserver] at finite
              dsimp [response] at childObserved finite
              dsimp [RecursiveResumptionSystem.leafObservation, Observer,
                genericRecursiveWriterObserver] at observed childObserved finite
              rw [childObserved] at observed
              rw [finite]
              exact observed
  | freeOp operation continuation ih =>
      simp [Observer, genericRecursiveWriterObserver, observeGenericWriter] at observed

theorem functional_monotone
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    ∀ {lower upper}, FlatApproximation.LE lower upper →
      FlatApproximation.LE
        (system.functional (Observer Result) handler lower)
        (system.functional (Observer Result) handler upper) := by
  intro lower upper bound state outcome observed
  unfold RecursiveResumptionSystem.functional at observed ⊢
  apply observe_mono _ _ observed
  intro leaf result leafObserved
  cases leaf with
  | inl value => exact leafObserved
  | inr next => exact bound next result leafObserved

theorem functional_continuous
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    FlatApproximation.OmegaContinuous
      (system.functional (Observer Result) handler) where
  monotone := by
    exact functional_monotone system handler
  preservesSup := by
    intro chain
    apply FlatApproximation.le_antisymm
    · intro state outcome observed
      unfold RecursiveResumptionSystem.functional at observed
      obtain ⟨index, finite⟩ := observe_sup_witness chain
        (FreeExtension.shallow handler (system.step state)) observed
      exact (FlatApproximation.Chain.mk
        (fun index => system.functional (Observer Result) handler
          (chain.sequence index))
        (fun index => functional_monotone system handler
          (chain.step index))).sup_of_observed finite
    · apply FlatApproximation.Chain.sup_le
      intro index state outcome observed
      exact functional_monotone system handler
        (chain.le_sup index) state outcome observed

/-- A direct fuel-indexed run: one outer constructor records the recursive
step, while the finite layer is evaluated by the Writer machine. -/
def LayerRunsFuel
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature)
    (fuel : Nat) (tree : FreeExtension writerBaseSignature
      userOperationSignature (Result ⊕ State))
    (outcome : List Val × Result) : Prop :=
  (Observer Result).observe
      (RecursiveResumptionSystem.leafObservation (Observer Result)
        (FlatApproximation.iterate
          (system.functional (Observer Result) handler) fuel))
      tree = some outcome

inductive RunsFuel
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    Nat → State → (List Val × Result) → Prop where
  | step : LayerRunsFuel system handler fuel
      (FreeExtension.shallow handler (system.step state)) outcome →
      RunsFuel system handler (fuel + 1) state outcome

theorem runsFuel_iff
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    RunsFuel system handler fuel state outcome ↔
      FlatApproximation.iterate
        (system.functional (Observer Result) handler) fuel state = some outcome := by
  cases fuel with
  | zero =>
      constructor
      · intro runs; cases runs
      · intro observed; cases observed
  | succ fuel =>
      constructor
      · intro runs
        cases runs with
        | step layer => exact layer
      · intro observed
        exact .step observed

def Runs
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature)
    (state : State) (outcome : List Val × Result) : Prop :=
  ∃ fuel, RunsFuel system handler fuel state outcome

theorem finite_adequacy
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    Runs system handler state outcome ↔
      ∃ fuel, FlatApproximation.iterate
        (system.functional (Observer Result) handler) fuel state = some outcome := by
  constructor <;> rintro ⟨fuel, observed⟩
  · exact ⟨fuel, (runsFuel_iff system handler).mp observed⟩
  · exact ⟨fuel, (runsFuel_iff system handler).mpr observed⟩

def model
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    GenericRecursiveResumption system (Observer Result) handler where
  continuous := functional_continuous system handler
  Runs := Runs system handler
  finiteAdequacy := finite_adequacy system handler
  pole := fun _ _ => True
  layerPreservesPole := fun _ _ _ _ _ => trivial

theorem limit_adequacy
    (system : RecursiveResumptionSystem
      writerBaseSignature userOperationSignature State Result)
    (handler : FreeExtension.AffineHandler
      writerBaseSignature userOperationSignature) :
    Runs system handler state outcome ↔
      (model system handler).semantics state = some outcome :=
  (model system handler).main.2.2.1

/-! ## A complete derived-deep Writer example -/

def exampleSystem : RecursiveResumptionSystem
    writerBaseSignature userOperationSignature Bool Unit where
  step
    | false => .baseOp (.tell .unit) (fun _ => .ret (.inl ()))
    | true => .freeOp ⟨0, 0, .unit⟩ (fun _ => .ret (.inr false))

def exampleHandler : FreeExtension.AffineHandler
    writerBaseSignature userOperationSignature where
  clause := fun _ => some (.ret .unit)

theorem example_iterate_false :
    FlatApproximation.iterate
      (exampleSystem.functional (Observer Unit) exampleHandler) 1 false =
        some ([.unit], ()) := rfl

theorem example_iterate_true :
    FlatApproximation.iterate
      (exampleSystem.functional (Observer Unit) exampleHandler) 2 true =
        some ([.unit], ()) := rfl

def examplePole (_state : Bool) (outcome : List Val × Unit) : Prop :=
  outcome = ([.unit], ())

theorem example_layer_preserves_pole (approximation) :
    FlatApproximation.Satisfies examplePole approximation →
      FlatApproximation.Satisfies examplePole
        (exampleSystem.functional (Observer Unit) exampleHandler approximation) := by
  intro satisfies state outcome observed
  cases state with
  | false =>
      simp only [RecursiveResumptionSystem.functional, exampleSystem,
        exampleHandler, FreeExtension.shallow, Observer,
        genericRecursiveWriterObserver, observeGenericWriter,
        RecursiveResumptionSystem.leafObservation] at observed
      exact (Option.some.inj observed).symm
  | true =>
      simp only [RecursiveResumptionSystem.functional, exampleSystem,
        exampleHandler, FreeExtension.shallow, FreeExtension.bind, Observer,
        genericRecursiveWriterObserver, observeGenericWriter,
        RecursiveResumptionSystem.leafObservation] at observed
      exact satisfies false outcome observed

def exampleModel : GenericRecursiveResumption
    exampleSystem (Observer Unit) exampleHandler where
  continuous := functional_continuous exampleSystem exampleHandler
  Runs := Runs exampleSystem exampleHandler
  finiteAdequacy := finite_adequacy exampleSystem exampleHandler
  pole := examplePole
  layerPreservesPole := example_layer_preserves_pole

theorem example_limit_true :
    exampleModel.semantics true = some ([.unit], ()) :=
  FlatApproximation.lfp_of_iterate exampleModel.continuous example_iterate_true

theorem example_recursive_pole :
    FlatApproximation.Satisfies examplePole exampleModel.semantics :=
  exampleModel.main.2.2.2

end GenericRecursiveWriter
end EffectSemantics
