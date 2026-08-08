import EffectSemantics.Recursive.DeepWriterObservation

namespace EffectSemantics

theorem DeepWriterApproximation.le_antisymm
    {left right : DeepWriterApproximation}
    (leftRight : LE left right) (rightLeft : LE right left) : left = right := by
  funext term
  apply Option.ext
  intro result
  constructor
  · exact leftRight term result
  · exact rightLeft term result

/-- Increasing chains of whole-program Writer approximations. -/
structure DeepWriterChain where
  sequence : Nat → DeepWriterApproximation
  step : ∀ index, DeepWriterApproximation.LE
    (sequence index) (sequence (index + 1))

theorem DeepWriterChain.le_add (chain : DeepWriterChain)
    (index extra : Nat) :
    DeepWriterApproximation.LE (chain.sequence index)
      (chain.sequence (index + extra)) := by
  induction extra with
  | zero => exact fun _ _ observed => observed
  | succ extra ih =>
      rw [Nat.add_succ]
      exact fun term result observed => chain.step _ term result
        (ih term result observed)

theorem DeepWriterChain.mono (chain : DeepWriterChain)
    {lower upper : Nat} (bound : lower ≤ upper) :
    DeepWriterApproximation.LE (chain.sequence lower) (chain.sequence upper) := by
  obtain ⟨extra, rfl⟩ := Nat.le.dest bound
  exact chain.le_add lower extra

noncomputable def DeepWriterChain.sup (chain : DeepWriterChain) :
    DeepWriterApproximation := fun term => by
  classical
  by_cases existsObserved : ∃ index result,
      chain.sequence index term = some result
  · exact some (Classical.choose (Classical.choose_spec existsObserved))
  · exact none

theorem DeepWriterChain.sup_of_observed (chain : DeepWriterChain)
    (observed : chain.sequence index term = some result) :
    chain.sup term = some result := by
  classical
  unfold DeepWriterChain.sup
  split
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenResult := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved : chain.sequence chosenIndex term = some chosenResult :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    let common := Nat.max index chosenIndex
    have originalAtCommon := chain.mono (Nat.le_max_left index chosenIndex)
      term result observed
    have chosenAtCommon := chain.mono (Nat.le_max_right index chosenIndex)
      term chosenResult chosenObserved
    have equal : chosenResult = result := by
      rw [originalAtCommon] at chosenAtCommon
      exact (Option.some.inj chosenAtCommon).symm
    change some chosenResult = some result
    rw [equal]
  next absent => exact False.elim (absent ⟨index, result, observed⟩)

theorem DeepWriterChain.sup_some_witness (chain : DeepWriterChain)
    (observed : chain.sup term = some result) :
    ∃ index, chain.sequence index term = some result := by
  classical
  unfold DeepWriterChain.sup at observed
  split at observed
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenResult := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved : chain.sequence chosenIndex term = some chosenResult :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have equal : chosenResult = result := Option.some.inj observed
    exact ⟨chosenIndex, by simpa [equal] using chosenObserved⟩
  next absent => cases observed

theorem DeepWriterChain.le_sup (chain : DeepWriterChain) (index : Nat) :
    DeepWriterApproximation.LE (chain.sequence index) chain.sup := by
  intro term result observed
  exact chain.sup_of_observed observed

def DeepWriterChain.map (chain : DeepWriterChain) (interface : Nat)
    (handler : AffineHandler) : DeepWriterChain where
  sequence index := deepWriterFunctional interface handler (chain.sequence index)
  step index := deepWriterFunctional_monotone (chain.step index)

/-- The recursive Writer-handler functional is ω-continuous: observing one
unfolding at a chain supremum already uses one finite member of the chain. -/
theorem deepWriterFunctional_preservesSup (chain : DeepWriterChain)
    (interface : Nat) (handler : AffineHandler) :
    deepWriterFunctional interface handler chain.sup =
      (chain.map interface handler).sup := by
  apply DeepWriterApproximation.le_antisymm
  · intro term result observed
    unfold deepWriterFunctional at observed
    cases found : term.head with
    | returned value =>
        exact (chain.map interface handler).sup_of_observed
          (index := 0) (by simpa [DeepWriterChain.map,
            deepWriterFunctional, found] using observed)
    | internal next =>
        simp only [found] at observed
        obtain ⟨index, finite⟩ := chain.sup_some_witness observed
        exact (chain.map interface handler).sup_of_observed
          (index := index) (by simpa [DeepWriterChain.map,
            deepWriterFunctional, found] using finite)
    | base request =>
        by_cases selected : request.operation = 0
        · simp only [found, selected, if_pos, Option.map_eq_some_iff] at observed
          obtain ⟨tail, tailObserved, transformed⟩ := observed
          obtain ⟨index, finite⟩ := chain.sup_some_witness tailObserved
          apply (chain.map interface handler).sup_of_observed (index := index)
          simp only [DeepWriterChain.map, deepWriterFunctional, found,
            selected, if_pos, Option.map_eq_some_iff]
          exact ⟨tail, finite, transformed⟩
        · simp [found, selected] at observed
    | free request =>
        by_cases same : request.interface = interface
        · cases clauseFound : handler.lookup request.operation with
          | none => simp [found, same, clauseFound] at observed
          | some clause =>
              simp only [found, same, if_pos, clauseFound] at observed
              obtain ⟨index, finite⟩ := chain.sup_some_witness observed
              apply (chain.map interface handler).sup_of_observed (index := index)
              simpa [DeepWriterChain.map, deepWriterFunctional, found, same,
                clauseFound] using finite
        · simp [found, same] at observed
    | stuck => simp [found] at observed
  · intro term result observed
    obtain ⟨index, finite⟩ :=
      (chain.map interface handler).sup_some_witness observed
    exact deepWriterFunctional_monotone (chain.le_sup index) term result finite

def deepWriterKleeneChain (interface : Nat)
    (handler : AffineHandler) : DeepWriterChain where
  sequence := iterateDeepWriter interface handler
  step index := by
    induction index with
    | zero => simp [iterateDeepWriter, DeepWriterApproximation.LE]
    | succ index ih => exact deepWriterFunctional_monotone ih

theorem deepWriterKleeneSup_eq_limit (interface : Nat)
    (handler : AffineHandler) :
    (deepWriterKleeneChain interface handler).sup =
      deepWriterLimitFamily interface handler := by
  apply DeepWriterApproximation.le_antisymm
  · intro term result observed
    obtain ⟨index, finite⟩ :=
      (deepWriterKleeneChain interface handler).sup_some_witness observed
    exact iterateDeepWriter_le_limit index interface handler term result finite
  · intro term result observed
    obtain ⟨fuel, finite⟩ := Comp.deepWriterLimit_some_witness observed
    rw [observeDeepWriter_eq_iterate] at finite
    exact (deepWriterKleeneChain interface handler).sup_of_observed finite

theorem iterateDeepWriter_le_prefixed
    (prefixed : DeepWriterApproximation.LE
      (deepWriterFunctional interface handler candidate) candidate) :
    ∀ fuel, DeepWriterApproximation.LE
      (iterateDeepWriter interface handler fuel) candidate
  | 0 => by simp [iterateDeepWriter, DeepWriterApproximation.LE]
  | fuel + 1 => fun term result observed =>
      prefixed term result
        (deepWriterFunctional_monotone
          (iterateDeepWriter_le_prefixed prefixed fuel) term result observed)

/-- The operational deep-handler limit is the least pre-fixed point of its
one-layer semantic functional, not merely an arbitrary solution. -/
theorem deepWriterLimit_le_prefixed
    (prefixed : DeepWriterApproximation.LE
      (deepWriterFunctional interface handler candidate) candidate) :
    DeepWriterApproximation.LE
      (deepWriterLimitFamily interface handler) candidate := by
  rw [← deepWriterKleeneSup_eq_limit interface handler]
  intro term result observed
  obtain ⟨fuel, finite⟩ :=
    (deepWriterKleeneChain interface handler).sup_some_witness observed
  exact iterateDeepWriter_le_prefixed prefixed fuel term result finite

theorem deepWriterLimit_le_fixed
    (fixed : deepWriterFunctional interface handler candidate = candidate) :
    DeepWriterApproximation.LE
      (deepWriterLimitFamily interface handler) candidate :=
  deepWriterLimit_le_prefixed (by rw [fixed]; exact fun _ _ observed => observed)

end EffectSemantics
