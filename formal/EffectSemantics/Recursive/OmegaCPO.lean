import EffectSemantics.Recursive.FiniteObservation

namespace EffectSemantics

theorem PartialObservation.le_antisymm {left right : PartialObservation}
    (leftRight : left ≤ right) (rightLeft : right ≤ left) : left = right := by
  apply PartialObservation.ext
  funext fuel
  cases leftFound : left.observeAt fuel with
  | none =>
      cases rightFound : right.observeAt fuel with
      | none => rfl
      | some outcome =>
          have := rightLeft fuel outcome rightFound
          rw [leftFound] at this
          cases this
  | some outcome =>
      have rightFound := leftRight fuel outcome leftFound
      rw [rightFound]

/-- An increasing ω-chain in the finite-observation approximation order. -/
structure ObservationChain where
  sequence : Nat → PartialObservation
  step : ∀ index, sequence index ≤ sequence (index + 1)

theorem ObservationChain.le_add (chain : ObservationChain)
    (index extra : Nat) : chain.sequence index ≤ chain.sequence (index + extra) := by
  induction extra with
  | zero => simpa using PartialObservation.le_refl (chain.sequence index)
  | succ extra ih =>
      rw [Nat.add_succ]
      exact PartialObservation.le_trans ih (chain.step (index + extra))

theorem ObservationChain.mono (chain : ObservationChain)
    {lower upper : Nat} (bound : lower ≤ upper) :
    chain.sequence lower ≤ chain.sequence upper := by
  obtain ⟨extra, rfl⟩ := Nat.le.dest bound
  exact chain.le_add lower extra

noncomputable def ObservationChain.supAt
    (chain : ObservationChain) (fuel : Nat) : Option FiniteOutcome := by
  classical
  by_cases existsObserved : ∃ index outcome,
      (chain.sequence index).observeAt fuel = some outcome
  · exact some (Classical.choose (Classical.choose_spec existsObserved))
  · exact none

theorem ObservationChain.supAt_of_observed (chain : ObservationChain)
    (observed : (chain.sequence index).observeAt fuel = some outcome) :
    chain.supAt fuel = some outcome := by
  classical
  unfold ObservationChain.supAt
  split
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenOutcome := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        (chain.sequence chosenIndex).observeAt fuel = some chosenOutcome :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    let common := Nat.max index chosenIndex
    have originalAtCommon := chain.mono (Nat.le_max_left index chosenIndex)
      fuel outcome observed
    have chosenAtCommon := chain.mono (Nat.le_max_right index chosenIndex)
      fuel chosenOutcome chosenObserved
    have equal : chosenOutcome = outcome := by
      rw [originalAtCommon] at chosenAtCommon
      exact (Option.some.inj chosenAtCommon).symm
    simp [chosenOutcome, equal]
  next absent => exact False.elim (absent ⟨index, outcome, observed⟩)

theorem ObservationChain.supAt_some_witness (chain : ObservationChain)
    (observed : chain.supAt fuel = some outcome) :
    ∃ index, (chain.sequence index).observeAt fuel = some outcome := by
  classical
  unfold ObservationChain.supAt at observed
  split at observed
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenOutcome := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        (chain.sequence chosenIndex).observeAt fuel = some chosenOutcome :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have equal : chosenOutcome = outcome := Option.some.inj observed
    exact ⟨chosenIndex, by simpa [equal] using chosenObserved⟩
  next absent => cases observed

noncomputable def ObservationChain.sup (chain : ObservationChain) :
    PartialObservation where
  observeAt := chain.supAt
  stable := by
    intro fuel outcome observed
    obtain ⟨index, atIndex⟩ := chain.supAt_some_witness observed
    exact chain.supAt_of_observed
      ((chain.sequence index).stable atIndex)

theorem ObservationChain.le_sup (chain : ObservationChain) (index : Nat) :
    chain.sequence index ≤ chain.sup := by
  intro fuel outcome observed
  exact chain.supAt_of_observed observed

theorem ObservationChain.sup_le (chain : ObservationChain)
    {upper : PartialObservation}
    (isUpper : ∀ index, chain.sequence index ≤ upper) :
    chain.sup ≤ upper := by
  intro fuel outcome observed
  obtain ⟨index, atIndex⟩ := chain.supAt_some_witness observed
  exact isUpper index fuel outcome atIndex

end EffectSemantics
