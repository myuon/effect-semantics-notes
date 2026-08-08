import EffectSemantics.Recursive.StableObservation

namespace EffectSemantics
namespace StableObservation

def mapOutcome (transform : Source → Target)
    (observation : StableObservation Source) : StableObservation Target where
  observeAt fuel := (observation.observeAt fuel).map transform
  stable := by
    intro fuel outcome observed
    simp only [Option.map_eq_some_iff] at observed ⊢
    obtain ⟨source, sourceObserved, rfl⟩ := observed
    exact ⟨source, observation.stable sourceObserved, rfl⟩

theorem mapOutcome_mono (transform : Source → Target)
    {lower upper : StableObservation Source} (bound : lower ≤ upper) :
    mapOutcome transform lower ≤ mapOutcome transform upper := by
  intro fuel outcome observed
  simp only [mapOutcome, Option.map_eq_some_iff] at observed ⊢
  obtain ⟨source, sourceObserved, transformed⟩ := observed
  exact ⟨source, bound fuel source sourceObserved, transformed⟩

def Chain.mapOutcome (chain : Chain Source) (transform : Source → Target) :
    Chain Target where
  sequence index := StableObservation.mapOutcome transform (chain.sequence index)
  step index := mapOutcome_mono transform (chain.step index)

theorem mapOutcome_preservesSup (chain : Chain Source)
    (transform : Source → Target) :
    mapOutcome transform chain.sup = (chain.mapOutcome transform).sup := by
  apply le_antisymm
  · intro fuel outcome observed
    simp only [mapOutcome, Option.map_eq_some_iff] at observed
    obtain ⟨source, sourceObserved, transformed⟩ := observed
    obtain ⟨index, finite⟩ := chain.supAt_some_witness sourceObserved
    apply (chain.mapOutcome transform).supAt_of_observed (index := index)
    change Option.map transform ((chain.sequence index).observeAt fuel) =
      some outcome
    exact Option.map_eq_some_iff.mpr ⟨source, finite, transformed⟩
  · intro fuel outcome observed
    obtain ⟨index, finite⟩ :=
      (chain.mapOutcome transform).supAt_some_witness observed
    change (mapOutcome transform (chain.sequence index)).observeAt fuel =
      some outcome at finite
    exact mapOutcome_mono transform (chain.le_sup index) fuel outcome finite

theorem mapOutcome_bottom (transform : Source → Target) :
    mapOutcome transform (bottom : StableObservation Source) = bottom := rfl

theorem mapOutcome_iterate
    {Source : Type u} {Target : Type v}
    {sourceFunction : StableObservation Source → StableObservation Source}
    {targetFunction : StableObservation Target → StableObservation Target}
    (transform : Source → Target)
    (commutes : ∀ observation : StableObservation Source,
      mapOutcome transform (sourceFunction observation) =
        targetFunction (mapOutcome transform observation)) :
    ∀ index,
      mapOutcome transform (iterate sourceFunction index) =
        iterate targetFunction index
  | 0 => mapOutcome_bottom transform
  | index + 1 => by
      rw [iterate, commutes, mapOutcome_iterate transform commutes index]
      rfl

/-- Fixed-point/morphism lifting: a result transformation commuting with one
semantic unfolding also commutes with the recursively defined least fixed
points. -/
theorem mapOutcome_lfp
    {Source : Type u} {Target : Type v}
    {sourceFunction : StableObservation Source → StableObservation Source}
    {targetFunction : StableObservation Target → StableObservation Target}
    (transform : Source → Target)
    (sourceContinuous : OmegaContinuous sourceFunction)
    (targetContinuous : OmegaContinuous targetFunction)
    (commutes : ∀ observation : StableObservation Source,
      mapOutcome transform (sourceFunction observation) =
        targetFunction (mapOutcome transform observation)) :
    mapOutcome transform (lfp sourceFunction sourceContinuous) =
      lfp targetFunction targetContinuous := by
  unfold lfp
  rw [mapOutcome_preservesSup]
  apply le_antisymm
  · intro fuel outcome observed
    obtain ⟨index, finite⟩ :=
      Chain.supAt_some_witness
        ((kleeneChain sourceFunction sourceContinuous).mapOutcome transform)
        observed
    have equal := mapOutcome_iterate transform commutes index
    change (mapOutcome transform (iterate sourceFunction index)).observeAt fuel =
      some outcome at finite
    rw [equal] at finite
    exact (kleeneChain targetFunction targetContinuous).supAt_of_observed finite
  · intro fuel outcome observed
    obtain ⟨index, finite⟩ :=
      (kleeneChain targetFunction targetContinuous).supAt_some_witness observed
    have equal := mapOutcome_iterate transform commutes index
    apply Chain.supAt_of_observed
      ((kleeneChain sourceFunction sourceContinuous).mapOutcome transform)
      (index := index)
    change (mapOutcome transform (iterate sourceFunction index)).observeAt fuel =
      some outcome
    rw [equal]
    exact finite

def BinaryAdmissible
    (relation : StableObservation Left → StableObservation Right → Prop) : Prop :=
  ∀ leftChain : Chain Left, ∀ rightChain : Chain Right,
    (∀ index, relation (leftChain.sequence index)
      (rightChain.sequence index)) →
    relation leftChain.sup rightChain.sup

/-- Relation lifting through recursion.  An admissible relation containing
the two bottoms and preserved by one unfolding relates the two least fixed
points. -/
theorem lfp_related
    {Left : Type u} {Right : Type v}
    {relation : StableObservation Left → StableObservation Right → Prop}
    {leftFunction : StableObservation Left → StableObservation Left}
    {rightFunction : StableObservation Right → StableObservation Right}
    (leftContinuous : OmegaContinuous leftFunction)
    (rightContinuous : OmegaContinuous rightFunction)
    (admissible : BinaryAdmissible relation)
    (bottomRelated : relation
      (bottom : StableObservation Left) (bottom : StableObservation Right))
    (closed : ∀ left right, relation left right →
      relation (leftFunction left) (rightFunction right)) :
    relation (lfp leftFunction leftContinuous : StableObservation Left)
      (lfp rightFunction rightContinuous : StableObservation Right) := by
  unfold lfp
  apply admissible (kleeneChain leftFunction leftContinuous)
    (kleeneChain rightFunction rightContinuous)
  intro index
  induction index with
  | zero => exact bottomRelated
  | succ index ih => exact closed _ _ ih

end StableObservation
end EffectSemantics
