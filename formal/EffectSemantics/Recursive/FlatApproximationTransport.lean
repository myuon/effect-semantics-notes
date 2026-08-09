import EffectSemantics.Recursive.FlatApproximation

namespace EffectSemantics.FlatApproximation

def mapOutcome (transform : Source → Target)
    (source : Carrier Term Source) : Carrier Term Target :=
  fun term => (source term).map transform

theorem mapOutcome_monotone (transform : Source → Target)
    (bound : LE lower upper) :
    LE (mapOutcome transform lower) (mapOutcome transform upper) := by
  intro term result observed
  simp only [mapOutcome, Option.map_eq_some_iff] at observed ⊢
  obtain ⟨source, sourceObserved, rfl⟩ := observed
  exact ⟨source, bound term source sourceObserved, rfl⟩

theorem mapOutcome_bottom (transform : Source → Target) :
    mapOutcome transform (bottom : Carrier Term Source) = bottom := rfl

def Chain.mapOutcome (chain : Chain Term Source) (transform : Source → Target) :
    Chain Term Target where
  sequence index := EffectSemantics.FlatApproximation.mapOutcome transform
    (chain.sequence index)
  step index := mapOutcome_monotone transform (chain.step index)

theorem mapOutcome_sup (chain : Chain Term Source) (transform : Source → Target) :
    mapOutcome transform chain.sup = (chain.mapOutcome transform).sup := by
  apply le_antisymm
  · intro term target observed
    simp only [mapOutcome, Option.map_eq_some_iff] at observed
    obtain ⟨source, sourceObserved, rfl⟩ := observed
    obtain ⟨index, finite⟩ := chain.sup_some_witness sourceObserved
    apply (chain.mapOutcome transform).sup_of_observed (index := index)
    change (chain.sequence index term).map transform = some (transform source)
    simp [finite]
  · intro term target observed
    obtain ⟨index, finite⟩ :=
      (chain.mapOutcome transform).sup_some_witness observed
    simp only [Chain.mapOutcome, mapOutcome, Option.map_eq_some_iff] at finite ⊢
    obtain ⟨source, sourceObserved, transformed⟩ := finite
    exact ⟨source, chain.sup_of_observed sourceObserved, transformed⟩

/-- A base outcome morphism commuting with one semantic layer commutes with
the completed recursive semantics. -/
theorem lfp_mapOutcome
    (sourceContinuous : OmegaContinuous sourceFunction)
    (targetContinuous : OmegaContinuous targetFunction)
    (commutes : ∀ approximation,
      mapOutcome transform (sourceFunction approximation) =
        targetFunction (mapOutcome transform approximation)) :
    mapOutcome transform (lfp sourceFunction sourceContinuous) =
      lfp targetFunction targetContinuous := by
  have iterateCommutes : ∀ fuel,
      mapOutcome transform (iterate sourceFunction fuel) =
        iterate targetFunction fuel := by
    intro fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
      rw [iterate, commutes, ih]
      rfl
  unfold lfp
  rw [mapOutcome_sup]
  apply le_antisymm
  · apply Chain.sup_le
    intro index
    change LE (mapOutcome transform (iterate sourceFunction index))
      (kleeneChain targetFunction targetContinuous).sup
    rw [iterateCommutes index]
    exact (kleeneChain targetFunction targetContinuous).le_sup index
  · apply Chain.sup_le
    intro index
    change LE (iterate targetFunction index)
      ((kleeneChain sourceFunction sourceContinuous).mapOutcome transform).sup
    rw [← iterateCommutes index]
    exact ((kleeneChain sourceFunction sourceContinuous).mapOutcome transform).le_sup
      index

/-- Synchronous admissibility for binary relations between recursive
approximations. -/
def BinaryAdmissible
    (relation : Carrier Term Left → Carrier Term Right → Prop) : Prop :=
  ∀ (left : Chain Term Left) (right : Chain Term Right),
    (∀ index, relation (left.sequence index) (right.sequence index)) →
      relation left.sup right.sup

theorem lfp_relation {Term Left Right : Type}
    {leftFunction : Carrier Term Left → Carrier Term Left}
    {rightFunction : Carrier Term Right → Carrier Term Right}
    {relation : Carrier Term Left → Carrier Term Right → Prop}
    (leftContinuous : OmegaContinuous leftFunction)
    (rightContinuous : OmegaContinuous rightFunction)
    (admissible : @BinaryAdmissible Term Left Right relation)
    (bottomRelated : relation
      (bottom : Carrier Term Left) (bottom : Carrier Term Right))
    (layerPreserved : ∀ {left right}, relation left right →
      relation (leftFunction left) (rightFunction right)) :
    relation (lfp leftFunction leftContinuous)
      (lfp rightFunction rightContinuous) := by
  unfold lfp
  apply admissible (kleeneChain leftFunction leftContinuous)
    (kleeneChain rightFunction rightContinuous)
  intro index
  induction index with
  | zero => exact bottomRelated
  | succ index ih => exact layerPreserved ih

/-- Pointwise outcome simulations form an admissible binary logical relation. -/
def OutcomeRel (outcomeRel : Left → Right → Prop)
    (left : Carrier Term Left) (right : Carrier Term Right) : Prop :=
  ∀ term leftOutcome, left term = some leftOutcome →
    ∃ rightOutcome, right term = some rightOutcome ∧
      outcomeRel leftOutcome rightOutcome

theorem outcomeRel_admissible {Term Left Right : Type}
    (outcomeRel : Left → Right → Prop) :
    @BinaryAdmissible Term Left Right
      (@OutcomeRel Left Right Term outcomeRel) := by
  intro left right all term leftOutcome observed
  obtain ⟨index, finite⟩ := left.sup_some_witness observed
  obtain ⟨rightOutcome, rightFinite, related⟩ :=
    all index term leftOutcome finite
  exact ⟨rightOutcome, right.sup_of_observed rightFinite, related⟩

end EffectSemantics.FlatApproximation
