import EffectSemantics.Denotational.StateTree

namespace EffectSemantics.Examples

open EffectSemantics StateTree

def stateTickHandler : StateTree.AffineSemantics where
  clause
    | 0 => some (fun _ => .ret .unit)
    | _ => none

def stateAroundTick : StateTree Val :=
  .put true (.free 0 0 .unit (fun _ =>
    .get (fun state => .ret (.bool state))))

theorem state_shallow_crosses_base :
    StateTree.shallow 0 stateTickHandler stateAroundTick =
      .put true (.get (fun state => .ret (.bool state))) := by
  rfl

theorem state_observation_preserved :
    StateTree.runClosed
      (StateTree.shallow 0 stateTickHandler stateAroundTick) false =
      some (.bool true, true) := by
  rfl

end EffectSemantics.Examples
