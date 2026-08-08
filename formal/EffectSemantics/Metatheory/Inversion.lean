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

structure LetView (sig : Signature) (ctx : Context) (bound body : Comp)
    (resultTy : Ty) (effect : Effect) where
  boundTy : Ty
  boundEffect : Effect
  bodyEffect : Effect
  boundTyping : HasComp sig ctx bound boundTy boundEffect
  bodyTyping : HasComp sig (boundTy :: ctx) body resultTy bodyEffect
  composedBelow : boundEffect * bodyEffect ≤ effect

def HasComp.letView {sig : Signature} {ctx : Context} {bound body : Comp}
    {resultTy : Ty} {effect : Effect}
    (typing : HasComp sig ctx (.letE bound body) resultTy effect) :
    LetView sig ctx bound body resultTy effect :=
  match typing with
  | .letE boundTyping bodyTyping =>
      ⟨_, _, _, boundTyping, bodyTyping, Effect.le_refl _⟩
  | .subeffect inner upperBound =>
      let view := inner.letView
      ⟨view.boundTy, view.boundEffect, view.bodyEffect,
        view.boundTyping, view.bodyTyping,
        Effect.le_trans view.composedBelow upperBound⟩

structure FreeOpView (sig : Signature) (ctx : Context)
    (interface operation : Nat) (parameter : Val) (resultTy : Ty)
    (effect : Effect) where
  parameterTy : Ty
  declaredResult : Ty
  lookup : sig.free interface operation = some ⟨parameterTy, declaredResult⟩
  parameterTyping : HasVal sig ctx parameter parameterTy
  resultEq : declaredResult = resultTy
  requestBelow : [EffectAtom.free interface] ≤ effect

def HasComp.freeOpView {sig : Signature} {ctx : Context}
    {interface operation : Nat} {parameter : Val} {resultTy : Ty}
    {effect : Effect}
    (typing : HasComp sig ctx (.freeOp interface operation parameter)
      resultTy effect) :
    FreeOpView sig ctx interface operation parameter resultTy effect :=
  match typing with
  | .freeOp lookup parameterTyping =>
      ⟨_, _, lookup, parameterTyping, rfl, Effect.le_refl _⟩
  | .subeffect inner upperBound =>
      let view := inner.freeOpView
      ⟨view.parameterTy, view.declaredResult, view.lookup,
        view.parameterTyping, view.resultEq,
        Effect.le_trans view.requestBelow upperBound⟩

structure BaseOpView (sig : Signature) (ctx : Context)
    (operation : Nat) (parameter : Val) (resultTy : Ty)
    (effect : Effect) where
  parameterTy : Ty
  declaredResult : Ty
  lookup : sig.base operation = some ⟨parameterTy, declaredResult⟩
  parameterTyping : HasVal sig ctx parameter parameterTy
  resultEq : declaredResult = resultTy
  requestBelow : [EffectAtom.base operation] ≤ effect

def HasComp.baseOpView {sig : Signature} {ctx : Context}
    {operation : Nat} {parameter : Val} {resultTy : Ty}
    {effect : Effect}
    (typing : HasComp sig ctx (.baseOp operation parameter) resultTy effect) :
    BaseOpView sig ctx operation parameter resultTy effect :=
  match typing with
  | .baseOp lookup parameterTyping =>
      ⟨_, _, lookup, parameterTyping, rfl, Effect.le_refl _⟩
  | .subeffect inner upperBound =>
      let view := inner.baseOpView
      ⟨view.parameterTy, view.declaredResult, view.lookup,
        view.parameterTyping, view.resultEq,
        Effect.le_trans view.requestBelow upperBound⟩

end EffectSemantics
