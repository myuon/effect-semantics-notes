import EffectSemantics.Metatheory.ContextTyping

namespace EffectSemantics

structure PlugView (sig : Signature) (ctx : Context) (evalCtx : EvalContext)
    (hole : Comp) (resultTy : Ty) (resultEffect : Effect) where
  holeTy : Ty
  holeEffect : Effect
  holeTyping : HasComp sig ctx hole holeTy holeEffect
  contextTyping : HasEvalContext sig ctx evalCtx holeTy holeEffect
    resultTy resultEffect

/-- Converse of typed plugging for the fine-grain `let` contexts. -/
def HasComp.plugView {sig : Signature} {ctx : Context} {evalCtx : EvalContext}
    {hole : Comp} {resultTy : Ty} {resultEffect : Effect}
    (typing : HasComp sig ctx (evalCtx.plug hole) resultTy resultEffect) :
    PlugView sig ctx evalCtx hole resultTy resultEffect :=
  match evalCtx with
  | [] => ⟨resultTy, resultEffect, typing, .hole⟩
  | .letE _ :: rest =>
      let outer := typing.plugView (evalCtx := rest)
      let frame := outer.holeTyping.letView
      ⟨frame.boundTy, frame.boundEffect, frame.boundTyping,
        .letE frame.bodyTyping frame.composedBelow outer.contextTyping⟩

structure TypedFreeRequest (sig : Signature) (ctx : Context)
    (request : FreeRequest) (resultTy : Ty) (resultEffect : Effect) where
  parameterTy : Ty
  responseTy : Ty
  holeEffect : Effect
  lookup : sig.free request.interface request.operation =
    some ⟨parameterTy, responseTy⟩
  parameterTyping : HasVal sig ctx request.parameter parameterTy
  contextTyping : HasEvalContext sig ctx request.context responseTy holeEffect
    resultTy resultEffect
  requestBelowHole : [EffectAtom.free request.interface] ≤ holeEffect

structure TypedBaseRequest (sig : Signature) (ctx : Context)
    (request : BaseRequest) (resultTy : Ty) (resultEffect : Effect) where
  parameterTy : Ty
  responseTy : Ty
  holeEffect : Effect
  lookup : sig.base request.operation = some ⟨parameterTy, responseTy⟩
  parameterTyping : HasVal sig ctx request.parameter parameterTy
  contextTyping : HasEvalContext sig ctx request.context responseTy holeEffect
    resultTy resultEffect
  requestBelowHole : [EffectAtom.base request.operation] ≤ holeEffect

def HasComp.exposedFreeView {sig : Signature} {ctx : Context}
    {request : FreeRequest} {resultTy : Ty} {resultEffect : Effect}
    (typing : HasComp sig ctx request.source resultTy resultEffect) :
    TypedFreeRequest sig ctx request resultTy resultEffect := by
  let plugged := typing.plugView (evalCtx := request.context)
  let operation := plugged.holeTyping.freeOpView
  rcases operation with ⟨parameterTy, declaredResult, lookup,
    parameterTyping, resultEq, requestBelow⟩
  cases resultEq
  exact ⟨parameterTy, plugged.holeTy, plugged.holeEffect, lookup,
    parameterTyping, plugged.contextTyping, requestBelow⟩

def HasComp.exposedBaseView {sig : Signature} {ctx : Context}
    {request : BaseRequest} {resultTy : Ty} {resultEffect : Effect}
    (typing : HasComp sig ctx request.source resultTy resultEffect) :
    TypedBaseRequest sig ctx request resultTy resultEffect := by
  let plugged := typing.plugView (evalCtx := request.context)
  let operation := plugged.holeTyping.baseOpView
  rcases operation with ⟨parameterTy, declaredResult, lookup,
    parameterTyping, resultEq, requestBelow⟩
  cases resultEq
  exact ⟨parameterTy, plugged.holeTy, plugged.holeEffect, lookup,
    parameterTyping, plugged.contextTyping, requestBelow⟩

def TypedFreeRequest.resumeTyping
    (requestTyping : TypedFreeRequest sig ctx request resultTy resultEffect)
    (responseTyping : HasVal sig ctx response requestTyping.responseTy) :
    HasComp sig ctx (request.resume response) resultTy resultEffect :=
  requestTyping.contextTyping.plugTyping
    ((HasComp.ret responseTyping).subeffect
      (Effect.le_trans (Effect.optional_free request.interface)
        requestTyping.requestBelowHole))

def TypedBaseRequest.resumeTyping
    (requestTyping : TypedBaseRequest sig ctx request resultTy resultEffect)
    (responseTyping : HasVal sig ctx response requestTyping.responseTy) :
    HasComp sig ctx (request.resume response) resultTy resultEffect :=
  requestTyping.contextTyping.plugTyping
    ((HasComp.ret responseTyping).subeffect
      (Effect.le_trans (Effect.nil_le [EffectAtom.base request.operation])
        requestTyping.requestBelowHole))

/-- The exposed interface occurs before a residual suffix in every declared
upper bound of the whole request term. -/
def HasComp.requestGradeFactor {sig : Signature} {ctx : Context}
    {request : FreeRequest} {resultTy : Ty} {resultEffect : Effect}
    (typing : HasComp sig ctx request.source resultTy resultEffect) :
    SuffixFactor [EffectAtom.free request.interface] resultEffect := by
  let view := typing.exposedFreeView
  exact view.contextTyping.factorSuffix view.requestBelowHole

/-- Under the concrete no-erasure subsequence preorder, an interface-free
upper bound cannot type a term currently exposing that interface. -/
theorem HasComp.noExposedFreeUnderFreeOf
    {sig : Signature} {ctx : Context} {request : FreeRequest}
    {resultTy : Ty} {resultEffect : Effect}
    (typing : HasComp sig ctx request.source resultTy resultEffect)
    (freeOf : Effect.FreeOf request.interface resultEffect) : False := by
  let factor := typing.requestGradeFactor
  exact Effect.factor_not_free factor.bound freeOf

end EffectSemantics
