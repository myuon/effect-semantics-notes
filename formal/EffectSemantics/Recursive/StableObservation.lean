namespace EffectSemantics

/-- A reusable flat finite-observation domain.  Once an outcome appears it
remains unchanged at all larger finite projections. -/
structure StableObservation (Outcome : Type u) where
  observeAt : Nat → Option Outcome
  stable : ∀ {fuel outcome}, observeAt fuel = some outcome →
    observeAt (fuel + 1) = some outcome

namespace StableObservation

def LE (left right : StableObservation Outcome) : Prop :=
  ∀ fuel outcome, left.observeAt fuel = some outcome →
    right.observeAt fuel = some outcome

instance : _root_.LE (StableObservation Outcome) := ⟨LE⟩

def bottom : StableObservation Outcome where
  observeAt _ := none
  stable := by intros; contradiction

theorem bottom_le (observation : StableObservation Outcome) :
    bottom ≤ observation := by
  intro _ _ impossible
  cases impossible

theorem le_refl (observation : StableObservation Outcome) :
    observation ≤ observation := fun _ _ observed => observed

theorem le_trans {first second third : StableObservation Outcome}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    first ≤ third := by
  intro fuel outcome observed
  exact secondThird fuel outcome (firstSecond fuel outcome observed)

@[ext] theorem ext {left right : StableObservation Outcome}
    (equal : left.observeAt = right.observeAt) : left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem le_antisymm {left right : StableObservation Outcome}
    (leftRight : left ≤ right) (rightLeft : right ≤ left) : left = right := by
  apply StableObservation.ext
  funext fuel
  cases leftFound : left.observeAt fuel with
  | none =>
      cases rightFound : right.observeAt fuel with
      | none => rfl
      | some outcome =>
          have impossible := rightLeft fuel outcome rightFound
          rw [leftFound] at impossible
          cases impossible
  | some outcome =>
      have rightFound := leftRight fuel outcome leftFound
      rw [rightFound]

structure Chain (Outcome : Type u) where
  sequence : Nat → StableObservation Outcome
  step : ∀ index, sequence index ≤ sequence (index + 1)

theorem Chain.le_add (chain : Chain Outcome) (index extra : Nat) :
    chain.sequence index ≤ chain.sequence (index + extra) := by
  induction extra with
  | zero => simpa using le_refl (chain.sequence index)
  | succ extra ih =>
      rw [Nat.add_succ]
      exact le_trans ih (chain.step (index + extra))

theorem Chain.mono (chain : Chain Outcome) {lower upper : Nat}
    (bound : lower ≤ upper) : chain.sequence lower ≤ chain.sequence upper := by
  obtain ⟨extra, rfl⟩ := Nat.le.dest bound
  exact chain.le_add lower extra

noncomputable def Chain.supAt (chain : Chain Outcome) (fuel : Nat) :
    Option Outcome := by
  classical
  by_cases existsObserved : ∃ index outcome,
      (chain.sequence index).observeAt fuel = some outcome
  · exact some (Classical.choose (Classical.choose_spec existsObserved))
  · exact none

theorem Chain.supAt_of_observed (chain : Chain Outcome)
    (observed : (chain.sequence index).observeAt fuel = some outcome) :
    chain.supAt fuel = some outcome := by
  classical
  unfold Chain.supAt
  split
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenOutcome := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        (chain.sequence chosenIndex).observeAt fuel = some chosenOutcome :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have originalAtCommon := chain.mono (Nat.le_max_left index chosenIndex)
      fuel outcome observed
    have chosenAtCommon := chain.mono (Nat.le_max_right index chosenIndex)
      fuel chosenOutcome chosenObserved
    have equal : chosenOutcome = outcome := by
      rw [originalAtCommon] at chosenAtCommon
      exact (Option.some.inj chosenAtCommon).symm
    change some chosenOutcome = some outcome
    rw [equal]
  next absent => exact False.elim (absent ⟨index, outcome, observed⟩)

theorem Chain.supAt_some_witness (chain : Chain Outcome)
    (observed : chain.supAt fuel = some outcome) :
    ∃ index, (chain.sequence index).observeAt fuel = some outcome := by
  classical
  unfold Chain.supAt at observed
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

noncomputable def Chain.sup (chain : Chain Outcome) :
    StableObservation Outcome where
  observeAt := chain.supAt
  stable := by
    intro fuel outcome observed
    obtain ⟨index, finite⟩ := chain.supAt_some_witness observed
    exact chain.supAt_of_observed ((chain.sequence index).stable finite)

theorem Chain.le_sup (chain : Chain Outcome) (index : Nat) :
    chain.sequence index ≤ chain.sup := by
  intro fuel outcome observed
  exact chain.supAt_of_observed observed

theorem Chain.sup_le (chain : Chain Outcome)
    {upper : StableObservation Outcome}
    (upperBound : ∀ index, chain.sequence index ≤ upper) :
    chain.sup ≤ upper := by
  intro fuel outcome observed
  obtain ⟨index, finite⟩ := chain.supAt_some_witness observed
  exact upperBound index fuel outcome finite

def iterate (function : StableObservation Outcome → StableObservation Outcome) :
    Nat → StableObservation Outcome
  | 0 => bottom
  | index + 1 => function (iterate function index)

structure OmegaContinuous
    (function : StableObservation Outcome → StableObservation Outcome) : Prop where
  monotone : ∀ {lower upper}, lower ≤ upper → function lower ≤ function upper
  preservesSup : ∀ chain : Chain Outcome,
    function chain.sup =
      (Chain.mk
        (fun index => function (chain.sequence index))
        (fun index => monotone (chain.step index))).sup

theorem iterate_step (continuous : OmegaContinuous function) (index : Nat) :
    iterate function index ≤ iterate function (index + 1) := by
  induction index with
  | zero => exact bottom_le _
  | succ index ih => exact continuous.monotone ih

def kleeneChain (function : StableObservation Outcome → StableObservation Outcome)
    (continuous : OmegaContinuous function) : Chain Outcome where
  sequence := iterate function
  step := iterate_step continuous

def Chain.map (chain : Chain Outcome)
    (function : StableObservation Outcome → StableObservation Outcome)
    (monotone : ∀ {lower upper}, lower ≤ upper → function lower ≤ function upper) :
    Chain Outcome where
  sequence index := function (chain.sequence index)
  step index := monotone (chain.step index)

noncomputable def lfp
    (function : StableObservation Outcome → StableObservation Outcome)
    (continuous : OmegaContinuous function) : StableObservation Outcome :=
  (kleeneChain function continuous).sup

theorem shifted_kleene_sup (continuous : OmegaContinuous function) :
    ((kleeneChain function continuous).map function continuous.monotone).sup =
      (kleeneChain function continuous).sup := by
  apply le_antisymm
  · apply Chain.sup_le
    intro index
    exact (kleeneChain function continuous).le_sup (index + 1)
  · apply Chain.sup_le
    intro index
    cases index with
    | zero => exact bottom_le _
    | succ index =>
        exact ((kleeneChain function continuous).map function
          continuous.monotone).le_sup index

theorem lfp_unfold (continuous : OmegaContinuous function) :
    function (lfp function continuous) = lfp function continuous := by
  rw [lfp, continuous.preservesSup]
  exact shifted_kleene_sup continuous

theorem lfp_le_prefixed (continuous : OmegaContinuous function)
    (prefixed : function candidate ≤ candidate) :
    lfp function continuous ≤ candidate := by
  apply Chain.sup_le
  intro index
  induction index with
  | zero => exact bottom_le _
  | succ index ih => exact le_trans (continuous.monotone ih) prefixed

theorem lfp_le_fixed (continuous : OmegaContinuous function)
    (fixed : function candidate = candidate) :
    lfp function continuous ≤ candidate :=
  lfp_le_prefixed continuous (by rw [fixed]; exact le_refl candidate)

def Satisfies (pole : Outcome → Prop)
    (observation : StableObservation Outcome) : Prop :=
  ∀ fuel outcome, observation.observeAt fuel = some outcome → pole outcome

theorem Satisfies.bottom (pole : Outcome → Prop) :
    Satisfies pole (bottom : StableObservation Outcome) := by
  intro _ _ impossible
  cases impossible

theorem Satisfies.sup (chain : Chain Outcome)
    (all : ∀ index, Satisfies pole (chain.sequence index)) :
    Satisfies pole chain.sup := by
  intro fuel outcome observed
  obtain ⟨index, finite⟩ := chain.supAt_some_witness observed
  exact all index fuel outcome finite

def Admissible (predicate : StableObservation Outcome → Prop) : Prop :=
  ∀ chain : Chain Outcome,
    (∀ index, predicate (chain.sequence index)) → predicate chain.sup

theorem satisfies_admissible (pole : Outcome → Prop) :
    Admissible (Satisfies pole) := fun chain all => Satisfies.sup chain all

theorem lfp_induction
    (continuous : OmegaContinuous function)
    (admissible : Admissible predicate)
    (atBottom : predicate bottom)
    (closed : ∀ observation, predicate observation →
      predicate (function observation)) :
    predicate (lfp function continuous) := by
  unfold lfp
  apply admissible (kleeneChain function continuous)
  intro index
  induction index with
  | zero => exact atBottom
  | succ index ih => exact closed _ ih

end StableObservation

end EffectSemantics
