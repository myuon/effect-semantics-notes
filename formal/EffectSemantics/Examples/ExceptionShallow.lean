import EffectSemantics.Denotational.ExceptionTree

namespace EffectSemantics.Examples

open EffectSemantics ExceptionTree

def exceptionTickHandler : ExceptionTree.AffineSemantics where
  clause
    | 0 => some (fun _ => .ret .unit)
    | _ => none

def raiseBeforeTick : ExceptionTree Val :=
  .raise (.bool false)

theorem exception_aborts_search :
    ExceptionTree.shallow 0 exceptionTickHandler raiseBeforeTick =
      .raise (.bool false) := rfl

def tickThenRaise : ExceptionTree Val :=
  .free 0 0 .unit (fun _ => .raise (.bool false))

theorem shallow_reaches_later_raise :
    ExceptionTree.shallow 0 exceptionTickHandler tickThenRaise =
      .raise (.bool false) := rfl

end EffectSemantics.Examples
