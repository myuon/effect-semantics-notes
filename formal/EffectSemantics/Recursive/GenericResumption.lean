import EffectSemantics.Denotational.GenericFreeExtension
import EffectSemantics.Recursive.FlatApproximationTransport

namespace EffectSemantics

/-!
# Base-independent recursive resumptions

A recursive system exposes one finite base/free tree at a time.  Leaves either
return a result or name the next recursive state.  Reinstalling a shallow
handler at every state produces the derived-deep one-layer functional.
-/

structure RecursiveResumptionSystem
    (base free : OperationSignature) (State Result : Type) where
  step : State → FreeExtension base free (Result ⊕ State)

/-- A finite observer folds a single extended tree once its leaves have been
assigned partial outcomes. -/
structure RecursiveFiniteObserver
    (base free : OperationSignature) (Result Outcome : Type) where
  returned : Result → Outcome
  observe : ∀ {Leaf : Type},
    (Leaf → Option Outcome) → FreeExtension base free Leaf → Option Outcome
  observeRet : ∀ {Leaf} (leaf : Leaf → Option Outcome) value,
    observe leaf (.ret value) = leaf value

namespace RecursiveResumptionSystem

def leafObservation
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (approximation : FlatApproximation.Carrier State Outcome) :
    Result ⊕ State → Option Outcome
  | .inl result => some (observer.returned result)
  | .inr next => approximation next

/-- One shallow pass followed by recursive calls through the supplied
approximation.  Its least fixed point is the derived-deep semantics. -/
def functional
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free) :
    FlatApproximation.Carrier State Outcome →
      FlatApproximation.Carrier State Outcome :=
  fun approximation state =>
    observer.observe (leafObservation observer approximation)
      (FreeExtension.shallow handler (system.step state))

/-- The same one-layer observer without installing a handler. -/
def unhandledFunctional
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome) :
    FlatApproximation.Carrier State Outcome →
      FlatApproximation.Carrier State Outcome :=
  fun approximation state =>
    observer.observe (leafObservation observer approximation) (system.step state)

theorem functional_eq_unhandled_of_baseOnly
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free)
    (old : ∀ state, FreeExtension.BaseOnly (system.step state)) :
    system.functional observer handler = system.unhandledFunctional observer := by
  funext approximation state
  unfold functional unhandledFunctional
  rw [(old state).shallow_eq handler]

end RecursiveResumptionSystem

/-- Precisely the two finite-observer facts needed for recursive Kleene
completion.  They separate base-specific observation from the generic fixed
point argument. -/
structure RecursiveObserverContinuity
    (observer : RecursiveFiniteObserver base free Result Outcome) where
  observeMono : ∀ {Leaf} {lower upper : Leaf → Option Outcome},
    (∀ leaf outcome, lower leaf = some outcome →
      upper leaf = some outcome) →
    ∀ tree outcome, observer.observe lower tree = some outcome →
      observer.observe upper tree = some outcome
  observeSupWitness : ∀ {State}
    (chain : FlatApproximation.Chain State Outcome)
    (tree : FreeExtension base free (Result ⊕ State)) (outcome),
    observer.observe
        (RecursiveResumptionSystem.leafObservation observer chain.sup) tree =
      some outcome →
    ∃ index, observer.observe
        (RecursiveResumptionSystem.leafObservation observer
          (chain.sequence index)) tree = some outcome

theorem RecursiveObserverContinuity.functionalContinuous
    {base free : OperationSignature} {State Result Outcome : Type}
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (cert : RecursiveObserverContinuity observer)
    (system : RecursiveResumptionSystem base free State Result)
    (handler : FreeExtension.AffineHandler base free) :
    FlatApproximation.OmegaContinuous
      (system.functional observer handler) where
  monotone := by
    intro lower upper bound state outcome observed
    unfold RecursiveResumptionSystem.functional at observed ⊢
    apply cert.observeMono _ _ _ observed
    intro leaf result leafObserved
    cases leaf with
    | inl value => exact leafObserved
    | inr next => exact bound next result leafObserved
  preservesSup := by
    intro chain
    let mapped : FlatApproximation.Chain State Outcome :=
      ⟨fun index => system.functional observer handler (chain.sequence index),
        fun index => by
          intro state outcome observed
          unfold RecursiveResumptionSystem.functional at observed ⊢
          apply cert.observeMono _ _ _ observed
          intro leaf result leafObserved
          cases leaf with
          | inl value => exact leafObserved
          | inr next => exact chain.step index next result leafObserved⟩
    apply FlatApproximation.le_antisymm
    · intro state outcome observed
      unfold RecursiveResumptionSystem.functional at observed
      obtain ⟨index, finite⟩ := cert.observeSupWitness chain
        (FreeExtension.shallow handler (system.step state)) outcome observed
      exact mapped.sup_of_observed finite
    · apply FlatApproximation.Chain.sup_le
      intro index state outcome observed
      unfold RecursiveResumptionSystem.functional at observed ⊢
      apply cert.observeMono _ _ _ observed
      intro leaf result leafObserved
      cases leaf with
      | inl value => exact leafObserved
      | inr next => exact chain.le_sup index next result leafObserved

/-- Executable fuel-indexed operational evaluator.  Each successor step runs
one finite exposed tree and recursively evaluates resumption leaves with one
less unit of fuel. -/
def genericRunFuel
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free) : Nat →
      FlatApproximation.Carrier State Outcome
  | 0 => FlatApproximation.bottom
  | fuel + 1 => fun state =>
      observer.observe
        (RecursiveResumptionSystem.leafObservation observer
          (genericRunFuel system observer handler fuel))
        (FreeExtension.shallow handler (system.step state))

theorem genericRunFuel_eq_iterate
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free) :
    genericRunFuel system observer handler fuel =
      FlatApproximation.iterate
        (system.functional observer handler) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [genericRunFuel, FlatApproximation.iterate]
      rw [ih]
      rfl

def GenericRuns
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free)
    (state : State) (outcome : Outcome) : Prop :=
  ∃ fuel, genericRunFuel system observer handler fuel state = some outcome

theorem genericFiniteAdequacy
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free) :
    GenericRuns system observer handler state outcome ↔
      ∃ fuel, FlatApproximation.iterate
        (system.functional observer handler) fuel state = some outcome := by
  constructor <;> rintro ⟨fuel, observed⟩
  · rw [genericRunFuel_eq_iterate system observer handler] at observed
    exact ⟨fuel, observed⟩
  · refine ⟨fuel, ?_⟩
    rw [genericRunFuel_eq_iterate system observer handler]
    exact observed

/-- Non-circular recursive certificate.  Finite-iterate adequacy and
one-layer pole preservation are local obligations; the completed semantics,
limit adequacy and recursive pole are derived. -/
structure GenericRecursiveResumptionCert
    (system : RecursiveResumptionSystem base free State Result)
    (observer : RecursiveFiniteObserver base free Result Outcome)
    (handler : FreeExtension.AffineHandler base free) where
  continuous : FlatApproximation.OmegaContinuous
    (system.functional observer handler)
  Runs : State → Outcome → Prop
  finiteAdequacy : ∀ {state outcome}, Runs state outcome ↔
    ∃ fuel, FlatApproximation.iterate
      (system.functional observer handler) fuel state = some outcome
  pole : State → Outcome → Prop
  layerPreservesPole : ∀ approximation,
    FlatApproximation.Satisfies pole approximation →
    FlatApproximation.Satisfies pole
      (system.functional observer handler approximation)

namespace GenericRecursiveResumptionCert

noncomputable def semantics
    {base free : OperationSignature} {State Result Outcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {observer : RecursiveFiniteObserver base free Result Outcome}
    {handler : FreeExtension.AffineHandler base free}
    (cert : GenericRecursiveResumptionCert system observer handler) :
    FlatApproximation.Carrier State Outcome :=
  FlatApproximation.lfp (system.functional observer handler) cert.continuous

/-- Generic recursive structure-preservation theorem for the resumption
calculus. -/
theorem main
    {base free : OperationSignature} {State Result Outcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {observer : RecursiveFiniteObserver base free Result Outcome}
    {handler : FreeExtension.AffineHandler base free}
    (cert : GenericRecursiveResumptionCert system observer handler) :
    (system.functional observer handler cert.semantics = cert.semantics) ∧
    (∀ {candidate},
      FlatApproximation.LE (system.functional observer handler candidate) candidate →
      FlatApproximation.LE cert.semantics candidate) ∧
    (∀ {state outcome}, cert.Runs state outcome ↔
      cert.semantics state = some outcome) ∧
    FlatApproximation.Satisfies cert.pole cert.semantics := by
  refine ⟨FlatApproximation.lfp_unfold cert.continuous,
    fun prefixed => FlatApproximation.lfp_le_prefixed cert.continuous prefixed,
    ?_, ?_⟩
  · intro state outcome
    rw [cert.finiteAdequacy]
    exact (FlatApproximation.lfp_some_iff cert.continuous).symm
  · apply FlatApproximation.lfp_induction cert.continuous
      (FlatApproximation.satisfies_admissible cert.pole)
      (FlatApproximation.Satisfies.bottom cert.pole)
    exact cert.layerPreservesPole

end GenericRecursiveResumptionCert

/-- Local one-layer commutation lifts an outcome morphism through the generic
recursive completion. -/
structure GenericRecursiveMorphismCert
    {base free : OperationSignature} {State Result SourceOutcome TargetOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {sourceObserver : RecursiveFiniteObserver base free Result SourceOutcome}
    {targetObserver : RecursiveFiniteObserver base free Result TargetOutcome}
    {handler : FreeExtension.AffineHandler base free}
    (source : GenericRecursiveResumptionCert system sourceObserver handler)
    (target : GenericRecursiveResumptionCert system targetObserver handler)
    (transform : SourceOutcome → TargetOutcome) where
  oneLayer : ∀ approximation,
    FlatApproximation.mapOutcome transform
        (system.functional sourceObserver handler approximation) =
      system.functional targetObserver handler
        (FlatApproximation.mapOutcome transform approximation)

theorem GenericRecursiveMorphismCert.lift
    {base free : OperationSignature} {State Result SourceOutcome TargetOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {sourceObserver : RecursiveFiniteObserver base free Result SourceOutcome}
    {targetObserver : RecursiveFiniteObserver base free Result TargetOutcome}
    {handler : FreeExtension.AffineHandler base free}
    {source : GenericRecursiveResumptionCert system sourceObserver handler}
    {target : GenericRecursiveResumptionCert system targetObserver handler}
    {transform : SourceOutcome → TargetOutcome}
    (cert : GenericRecursiveMorphismCert source target transform) :
    FlatApproximation.mapOutcome transform source.semantics = target.semantics :=
  FlatApproximation.lfp_mapOutcome source.continuous target.continuous cert.oneLayer

/-- Admissible binary relations preserved by one layer lift to the two least
fixed points. -/
structure GenericRecursiveRelationCert
    {base free : OperationSignature} {State Result LeftOutcome RightOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {leftObserver : RecursiveFiniteObserver base free Result LeftOutcome}
    {rightObserver : RecursiveFiniteObserver base free Result RightOutcome}
    {handler : FreeExtension.AffineHandler base free}
    (left : GenericRecursiveResumptionCert system leftObserver handler)
    (right : GenericRecursiveResumptionCert system rightObserver handler)
    (relation : FlatApproximation.Carrier State LeftOutcome →
      FlatApproximation.Carrier State RightOutcome → Prop) where
  admissible : FlatApproximation.BinaryAdmissible relation
  bottom : relation FlatApproximation.bottom FlatApproximation.bottom
  oneLayer : ∀ {leftApproximation rightApproximation},
    relation leftApproximation rightApproximation →
    relation
      (system.functional leftObserver handler leftApproximation)
      (system.functional rightObserver handler rightApproximation)

theorem GenericRecursiveRelationCert.lift
    {base free : OperationSignature} {State Result LeftOutcome RightOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {leftObserver : RecursiveFiniteObserver base free Result LeftOutcome}
    {rightObserver : RecursiveFiniteObserver base free Result RightOutcome}
    {handler : FreeExtension.AffineHandler base free}
    {left : GenericRecursiveResumptionCert system leftObserver handler}
    {right : GenericRecursiveResumptionCert system rightObserver handler}
    {relation : FlatApproximation.Carrier State LeftOutcome →
      FlatApproximation.Carrier State RightOutcome → Prop}
    (cert : GenericRecursiveRelationCert left right relation) :
    relation left.semantics right.semantics :=
  FlatApproximation.lfp_relation left.continuous right.continuous
    cert.admissible cert.bottom cert.oneLayer

/-- Recursive closure of an observation-sensitive outcome relation.  In the
intended use, `outcomeTT` is the finite TT relation obtained from
`GenericExtensionAlgebra.TTLayerCert`; only its one-layer preservation remains
to be checked at the resumption boundary. -/
structure GenericRecursiveOutcomeTTCert
    {base free : OperationSignature} {State Result LeftOutcome RightOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {leftObserver : RecursiveFiniteObserver base free Result LeftOutcome}
    {rightObserver : RecursiveFiniteObserver base free Result RightOutcome}
    {handler : FreeExtension.AffineHandler base free}
    (left : GenericRecursiveResumptionCert system leftObserver handler)
    (right : GenericRecursiveResumptionCert system rightObserver handler)
    (outcomeTT : LeftOutcome → RightOutcome → Prop) where
  oneLayer : ∀ {leftApproximation rightApproximation},
    FlatApproximation.OutcomeRel outcomeTT
      leftApproximation rightApproximation →
    FlatApproximation.OutcomeRel outcomeTT
      (system.functional leftObserver handler leftApproximation)
      (system.functional rightObserver handler rightApproximation)

theorem GenericRecursiveOutcomeTTCert.lift
    {base free : OperationSignature} {State Result LeftOutcome RightOutcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {leftObserver : RecursiveFiniteObserver base free Result LeftOutcome}
    {rightObserver : RecursiveFiniteObserver base free Result RightOutcome}
    {handler : FreeExtension.AffineHandler base free}
    {left : GenericRecursiveResumptionCert system leftObserver handler}
    {right : GenericRecursiveResumptionCert system rightObserver handler}
    {outcomeTT : LeftOutcome → RightOutcome → Prop}
    (cert : GenericRecursiveOutcomeTTCert left right outcomeTT) :
    FlatApproximation.OutcomeRel outcomeTT left.semantics right.semantics := by
  apply GenericRecursiveRelationCert.lift
    (left := left) (right := right)
    (relation := FlatApproximation.OutcomeRel outcomeTT)
  exact {
    admissible := FlatApproximation.outcomeRel_admissible outcomeTT
    bottom := by
      intro state leftOutcome impossible
      cases impossible
    oneLayer := cert.oneLayer
  }

/-- Recursive old-language conservativity: if no newly adjoined request can
occur in any exposed layer, reinstalling the shallow handler changes neither
the functional nor its least fixed point. -/
theorem GenericRecursiveResumptionCert.oldLanguageConservative
    {base free : OperationSignature} {State Result Outcome : Type}
    {system : RecursiveResumptionSystem base free State Result}
    {observer : RecursiveFiniteObserver base free Result Outcome}
    {handler : FreeExtension.AffineHandler base free}
    (cert : GenericRecursiveResumptionCert system observer handler)
    (old : ∀ state, FreeExtension.BaseOnly (system.step state)) :
    ∃ unhandledContinuous : FlatApproximation.OmegaContinuous
        (system.unhandledFunctional observer),
      cert.semantics = FlatApproximation.lfp
        (system.unhandledFunctional observer) unhandledContinuous := by
  have equal := system.functional_eq_unhandled_of_baseOnly observer handler old
  have unhandledContinuous : FlatApproximation.OmegaContinuous
      (system.unhandledFunctional observer) := by
    rw [← equal]
    exact cert.continuous
  refine ⟨unhandledContinuous, FlatApproximation.le_antisymm ?_ ?_⟩
  · apply cert.main.2.1
    rw [equal, FlatApproximation.lfp_unfold unhandledContinuous]
    exact FlatApproximation.le_refl _
  · apply FlatApproximation.lfp_le_prefixed unhandledContinuous
    rw [← equal, cert.main.1]
    exact FlatApproximation.le_refl _

end EffectSemantics
