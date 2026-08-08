import EffectSemantics.Metatheory.RenameSubst

namespace EffectSemantics

/-- Canonical information retained after stripping any number of outer
subeffecting rules from a typed return. -/
structure ReturnView (sig : Signature) (ctx : Context) (value : Val)
    (ty : Ty) (effect : Effect) where
  valueTyping : HasVal sig ctx value ty
  pureBelow : (1 : Effect) ≤ effect

def HasComp.returnView {sig : Signature} {ctx : Context} {value : Val}
    {ty : Ty} {effect : Effect}
    (typing : HasComp sig ctx (.ret value) ty effect) :
    ReturnView sig ctx value ty effect :=
  match typing with
  | .ret valueTyping => ⟨valueTyping, Effect.le_refl 1⟩
  | .subeffect inner bound =>
      let view := inner.returnView
      ⟨view.valueTyping, Effect.le_trans view.pureBelow bound⟩

end EffectSemantics
