import EffectSemantics.Operational.Boundary

namespace EffectSemantics

/-- An affine response handler.  A clause body binds only the operation
parameter.  Its returned value is fed exactly once to the captured source
continuation by the operational semantics. -/
structure AffineHandler where
  clauses : List (Nat × Comp)
  deriving DecidableEq, Repr

def AffineHandler.lookup (handler : AffineHandler) (operation : Nat) : Option Comp :=
  (handler.clauses.find? (fun clause => clause.1 = operation)).map Prod.snd

/-- Runtime states keep the shallow handler separate from source syntax. -/
inductive HandlerState where
  | core (term : Comp)
  | shallow (interface : Nat) (handler : AffineHandler) (term : Comp)
  deriving DecidableEq, Repr

end EffectSemantics
