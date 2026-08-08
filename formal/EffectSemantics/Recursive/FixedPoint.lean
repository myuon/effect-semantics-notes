import EffectSemantics.Recursive.OmegaCPO

namespace EffectSemantics

def PartialObservation.iterate
    (function : PartialObservation → PartialObservation) :
    Nat → PartialObservation
  | 0 => .bottom
  | fuel + 1 => function (iterate function fuel)

structure OmegaContinuous
    (function : PartialObservation → PartialObservation) : Prop where
  monotone : ∀ {lower upper}, lower ≤ upper →
    function lower ≤ function upper
  preservesSup : ∀ chain : ObservationChain,
    function chain.sup =
      (ObservationChain.mk
        (fun index => function (chain.sequence index))
        (fun index => monotone (chain.step index))).sup

theorem PartialObservation.iterate_step
    (continuous : OmegaContinuous function) (index : Nat) :
    iterate function index ≤ iterate function (index + 1) := by
  induction index with
  | zero => exact PartialObservation.bottom_le _
  | succ index ih => exact continuous.monotone ih

def PartialObservation.kleeneChain
    (function : PartialObservation → PartialObservation)
    (continuous : OmegaContinuous function) : ObservationChain where
  sequence := iterate function
  step := iterate_step continuous

noncomputable def PartialObservation.lfp
    (function : PartialObservation → PartialObservation)
    (continuous : OmegaContinuous function) : PartialObservation :=
  (kleeneChain function continuous).sup

def ObservationChain.map (chain : ObservationChain)
    (function : PartialObservation → PartialObservation)
    (monotone : ∀ {lower upper}, lower ≤ upper → function lower ≤ function upper) :
    ObservationChain where
  sequence index := function (chain.sequence index)
  step index := monotone (chain.step index)

theorem PartialObservation.shifted_kleene_sup
    (continuous : OmegaContinuous function) :
    (ObservationChain.map (kleeneChain function continuous) function
      continuous.monotone).sup =
      (kleeneChain function continuous).sup := by
  apply PartialObservation.le_antisymm
  · apply ObservationChain.sup_le
    intro index
    exact (kleeneChain function continuous).le_sup (index + 1)
  · apply ObservationChain.sup_le
    intro index
    cases index with
    | zero => exact PartialObservation.bottom_le _
    | succ index =>
        exact (ObservationChain.map (kleeneChain function continuous) function
          continuous.monotone).le_sup index

/-- Kleene's fixed-point equation on the concrete finite-observation ω-CPO. -/
theorem PartialObservation.lfp_unfold
    (continuous : OmegaContinuous function) :
    function (lfp function continuous) = lfp function continuous := by
  rw [lfp, continuous.preservesSup]
  exact shifted_kleene_sup continuous

theorem PartialObservation.lfp_le_prefixed
    (continuous : OmegaContinuous function)
    (prefixed : function candidate ≤ candidate) :
    lfp function continuous ≤ candidate := by
  apply ObservationChain.sup_le
  intro index
  induction index with
  | zero => exact PartialObservation.bottom_le candidate
  | succ index ih =>
      exact PartialObservation.le_trans (continuous.monotone ih) prefixed

theorem PartialObservation.lfp_le_fixed
    (continuous : OmegaContinuous function)
    (fixed : function candidate = candidate) :
    lfp function continuous ≤ candidate :=
  lfp_le_prefixed continuous (by
    rw [fixed]
    exact PartialObservation.le_refl candidate)

theorem PartialObservation.identityContinuous :
    OmegaContinuous (fun observation : PartialObservation => observation) := by
  refine { monotone := ?_, preservesSup := ?_ }
  · exact fun bound => bound
  · exact fun _chain => rfl

theorem PartialObservation.lfp_identity_bottom :
    lfp (fun observation : PartialObservation => observation)
      identityContinuous = bottom := by
  apply PartialObservation.le_antisymm
  · exact lfp_le_fixed identityContinuous rfl
  · exact PartialObservation.bottom_le _

end EffectSemantics
