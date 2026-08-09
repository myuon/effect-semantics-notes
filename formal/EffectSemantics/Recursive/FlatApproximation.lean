namespace EffectSemantics.FlatApproximation

abbrev Carrier (Term Outcome : Type) := Term → Option Outcome

def LE (lower upper : Carrier Term Outcome) : Prop :=
  ∀ term outcome, lower term = some outcome → upper term = some outcome

theorem le_refl (value : Carrier Term Outcome) : LE value value :=
  fun _ _ observed => observed

theorem le_trans {first second third : Carrier Term Outcome}
    (firstSecond : LE first second) (secondThird : LE second third) :
    LE first third := fun term outcome observed =>
  secondThird term outcome (firstSecond term outcome observed)

theorem le_antisymm {left right : Carrier Term Outcome}
    (leftRight : LE left right) (rightLeft : LE right left) : left = right := by
  funext term
  apply Option.ext
  intro outcome
  exact ⟨leftRight term outcome, rightLeft term outcome⟩

def bottom : Carrier Term Outcome := fun _ => none

theorem bottom_le (value : Carrier Term Outcome) : LE bottom value := by
  intro _ _ impossible
  cases impossible

structure Chain (Term Outcome : Type) where
  sequence : Nat → Carrier Term Outcome
  step : ∀ index, LE (sequence index) (sequence (index + 1))

theorem Chain.le_add (chain : Chain Term Outcome) (index extra : Nat) :
    LE (chain.sequence index) (chain.sequence (index + extra)) := by
  induction extra with
  | zero => exact le_refl _
  | succ extra ih =>
      rw [Nat.add_succ]
      exact le_trans ih (chain.step _)

theorem Chain.mono (chain : Chain Term Outcome) {lower upper : Nat}
    (bound : lower ≤ upper) : LE (chain.sequence lower) (chain.sequence upper) := by
  obtain ⟨extra, rfl⟩ := Nat.le.dest bound
  exact chain.le_add lower extra

noncomputable def Chain.sup (chain : Chain Term Outcome) : Carrier Term Outcome :=
  fun term => by
    classical
    by_cases existsObserved : ∃ index outcome,
        chain.sequence index term = some outcome
    · exact some (Classical.choose (Classical.choose_spec existsObserved))
    · exact none

theorem Chain.sup_of_observed (chain : Chain Term Outcome)
    (observed : chain.sequence index term = some outcome) :
    chain.sup term = some outcome := by
  classical
  unfold Chain.sup
  split
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenOutcome := Classical.choose (Classical.choose_spec existsObserved)
    have chosen : chain.sequence chosenIndex term = some chosenOutcome :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have left := chain.mono (Nat.le_max_left index chosenIndex) term outcome observed
    have right := chain.mono (Nat.le_max_right index chosenIndex) term chosenOutcome chosen
    have equal : chosenOutcome = outcome := by
      rw [left] at right
      exact (Option.some.inj right).symm
    exact congrArg some equal
  next absent => exact False.elim (absent ⟨index, outcome, observed⟩)

theorem Chain.sup_some_witness (chain : Chain Term Outcome)
    (observed : chain.sup term = some outcome) :
    ∃ index, chain.sequence index term = some outcome := by
  classical
  unfold Chain.sup at observed
  split at observed
  next existsObserved =>
    let chosenIndex := Classical.choose existsObserved
    let chosenOutcome := Classical.choose (Classical.choose_spec existsObserved)
    have chosen : chain.sequence chosenIndex term = some chosenOutcome :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have equal : chosenOutcome = outcome := Option.some.inj observed
    exact ⟨chosenIndex, by simpa [equal] using chosen⟩
  next absent => cases observed

theorem Chain.le_sup (chain : Chain Term Outcome) (index : Nat) :
    LE (chain.sequence index) chain.sup :=
  fun _ _ observed => chain.sup_of_observed observed

theorem Chain.sup_le (chain : Chain Term Outcome) {upper : Carrier Term Outcome}
    (bound : ∀ index, LE (chain.sequence index) upper) : LE chain.sup upper := by
  intro term outcome observed
  obtain ⟨index, finite⟩ := chain.sup_some_witness observed
  exact bound index term outcome finite

def iterate (function : Carrier Term Outcome → Carrier Term Outcome) :
    Nat → Carrier Term Outcome
  | 0 => bottom
  | fuel + 1 => function (iterate function fuel)

structure OmegaContinuous
    (function : Carrier Term Outcome → Carrier Term Outcome) : Prop where
  monotone : ∀ {lower upper}, LE lower upper → LE (function lower) (function upper)
  preservesSup : ∀ chain : Chain Term Outcome,
    function chain.sup = (Chain.mk
      (fun index => function (chain.sequence index))
      (fun index => monotone (chain.step index))).sup

theorem iterate_step (continuous : OmegaContinuous function) (index : Nat) :
    LE (iterate function index) (iterate function (index + 1)) := by
  induction index with
  | zero => exact bottom_le _
  | succ index ih => exact continuous.monotone ih

def kleeneChain (function : Carrier Term Outcome → Carrier Term Outcome)
    (continuous : OmegaContinuous function) : Chain Term Outcome where
  sequence := iterate function
  step := iterate_step continuous

noncomputable def lfp
    (function : Carrier Term Outcome → Carrier Term Outcome)
    (continuous : OmegaContinuous function) : Carrier Term Outcome :=
  (kleeneChain function continuous).sup

theorem lfp_unfold (continuous : OmegaContinuous function) :
    function (lfp function continuous) = lfp function continuous := by
  rw [lfp, continuous.preservesSup]
  apply le_antisymm
  · apply Chain.sup_le
    intro index
    exact (kleeneChain function continuous).le_sup (index + 1)
  · apply Chain.sup_le
    intro index
    cases index with
    | zero => exact bottom_le _
    | succ index =>
        exact (Chain.mk
          (fun index => function ((kleeneChain function continuous).sequence index))
          (fun index => continuous.monotone
            ((kleeneChain function continuous).step index))).le_sup index

theorem iterate_le_prefixed (continuous : OmegaContinuous function)
    (prefixed : LE (function candidate) candidate) :
    ∀ fuel, LE (iterate function fuel) candidate
  | 0 => bottom_le _
  | fuel + 1 => le_trans
      (continuous.monotone (iterate_le_prefixed continuous prefixed fuel)) prefixed

theorem lfp_le_prefixed (continuous : OmegaContinuous function)
    (prefixed : LE (function candidate) candidate) :
    LE (lfp function continuous) candidate := by
  apply Chain.sup_le
  exact iterate_le_prefixed continuous prefixed

theorem lfp_of_iterate (continuous : OmegaContinuous function)
    (observed : iterate function fuel term = some outcome) :
    lfp function continuous term = some outcome := by
  unfold lfp
  exact Chain.sup_of_observed _ observed

theorem lfp_some_witness (continuous : OmegaContinuous function)
    (observed : lfp function continuous term = some outcome) :
    ∃ fuel, iterate function fuel term = some outcome := by
  unfold lfp at observed
  exact Chain.sup_some_witness _ observed

theorem lfp_some_iff (continuous : OmegaContinuous function) :
    lfp function continuous term = some outcome ↔
      ∃ fuel, iterate function fuel term = some outcome :=
  ⟨lfp_some_witness continuous,
    fun ⟨_fuel, observed⟩ => lfp_of_iterate continuous observed⟩

def Satisfies (pole : Term → Outcome → Prop)
    (approximation : Carrier Term Outcome) : Prop :=
  ∀ term outcome, approximation term = some outcome → pole term outcome

theorem Satisfies.bottom (pole : Term → Outcome → Prop) :
    Satisfies pole (bottom : Carrier Term Outcome) := by
  intro _ _ impossible
  cases impossible

theorem Satisfies.sup (chain : Chain Term Outcome)
    (all : ∀ index, Satisfies pole (chain.sequence index)) :
    Satisfies pole chain.sup := by
  intro term outcome observed
  obtain ⟨index, finite⟩ := chain.sup_some_witness observed
  exact all index term outcome finite

def Admissible (predicate : Carrier Term Outcome → Prop) : Prop :=
  ∀ chain : Chain Term Outcome,
    (∀ index, predicate (chain.sequence index)) → predicate chain.sup

theorem satisfies_admissible (pole : Term → Outcome → Prop) :
    Admissible (Satisfies pole) := fun chain all => Satisfies.sup chain all

theorem lfp_induction
    (continuous : OmegaContinuous function)
    (admissible : Admissible predicate)
    (atBottom : predicate bottom)
    (closed : ∀ approximation, predicate approximation →
      predicate (function approximation)) :
    predicate (lfp function continuous) := by
  unfold lfp
  apply admissible (kleeneChain function continuous)
  intro index
  induction index with
  | zero => exact atBottom
  | succ index ih => exact closed _ ih

end EffectSemantics.FlatApproximation
