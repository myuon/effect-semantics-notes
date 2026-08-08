import EffectSemantics.Recursive.DeepApprox

namespace EffectSemantics.Examples

open EffectSemantics WriterTree

theorem two_ticks_one_approx :
    deepApprox 1 0 tickSemantics twoTicks =
      .free 0 0 .unit (fun _ => .ret .unit) := by
  exact shallow_two_ticks

theorem two_ticks_two_approximants :
    deepApprox 2 0 tickSemantics twoTicks = .ret .unit := by
  rfl

theorem partial_tock_remains (fuel : Nat) :
    deepApprox fuel 0 tickSemantics
      (.free 0 1 Val.unit (fun _ => .ret Val.unit)) =
      .free 0 1 Val.unit (fun _ => .ret Val.unit) := by
  apply WriterTree.deepApprox_fixed
  rfl

theorem tick_after_tock_one_approx :
    deepApprox 1 0 tickSemantics tickThenTock =
      .free 0 1 .unit (fun _ => .ret .unit) := by
  exact shallow_tick_after_tock

theorem tick_after_tock_stabilizes (fuel : Nat) :
    deepApprox (fuel + 1) 0 tickSemantics tickThenTock =
      .free 0 1 .unit (fun _ => .ret .unit) := by
  rw [WriterTree.deepApprox_succ, shallow_tick_after_tock]
  exact partial_tock_remains fuel

end EffectSemantics.Examples
