import EffectSemantics.Denotational.WriterTree

namespace EffectSemantics.Examples

open EffectSemantics WriterTree

def tickSemantics : AffineSemantics where
  clause
    | 0 => some (fun _ => .ret .unit)
    | _ => none

def twoTicks : WriterTree Val :=
  .free 0 0 .unit (fun _ =>
    .free 0 0 .unit (fun _ => .ret .unit))

/-- One shallow pass consumes only the first matching request. -/
theorem shallow_two_ticks :
    shallow 0 tickSemantics twoTicks =
      .free 0 0 .unit (fun _ => .ret .unit) := by
  unfold twoTicks
  rw [WriterTree.shallow_match tickSemantics (by rfl)]
  rfl

def tickThenTock : WriterTree Val :=
  .free 0 1 .unit (fun _ =>
    .free 0 0 .unit (fun _ => .ret .unit))

/-- A missing same-interface clause is crossed, so the later matching request
is selected. -/
theorem shallow_tick_after_tock :
    shallow 0 tickSemantics tickThenTock =
      .free 0 1 .unit (fun _ => .ret .unit) := by
  rfl

end EffectSemantics.Examples
