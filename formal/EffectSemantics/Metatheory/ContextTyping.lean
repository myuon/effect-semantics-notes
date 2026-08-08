import EffectSemantics.Metatheory.Preservation

namespace EffectSemantics

/-- Typing of an evaluation context from a hole computation to the final
computation. Frames are innermost first, matching `EvalContext.plug`. -/
inductive HasEvalContext (sig : Signature) (ctx : Context) :
    EvalContext → Ty → Effect → Ty → Effect → Type where
  | hole : HasEvalContext sig ctx [] holeTy holeEffect holeTy holeEffect
  | letE :
      HasComp sig (holeTy :: ctx) body frameTy bodyEffect →
      HasEvalContext sig ctx rest frameTy (holeEffect * bodyEffect)
        resultTy resultEffect →
      HasEvalContext sig ctx (.letE body :: rest) holeTy holeEffect
        resultTy resultEffect

def HasEvalContext.plugTyping
    {sig : Signature} {ctx : Context} {evalCtx : EvalContext}
    {holeTy resultTy : Ty} {holeEffect resultEffect : Effect}
    (contextTyping : HasEvalContext sig ctx evalCtx holeTy holeEffect
      resultTy resultEffect)
    {term : Comp} (termTyping : HasComp sig ctx term holeTy holeEffect) :
    HasComp sig ctx (evalCtx.plug term) resultTy resultEffect :=
  match contextTyping with
  | .hole => termTyping
  | .letE bodyTyping restTyping =>
      restTyping.plugTyping (.letE termTyping bodyTyping)

/-- A typed operation expression plugged into a typed context remains typed;
the continuation is obtained from the same context, not from source syntax. -/
def HasEvalContext.freeRequestTyping
    {sig : Signature} {ctx : Context} {evalCtx : EvalContext}
    {interface operation : Nat} {parameter : Val}
    {parameterTy responseTy resultTy : Ty} {resultEffect : Effect}
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (parameterTyping : HasVal sig ctx parameter parameterTy)
    (contextTyping : HasEvalContext sig ctx evalCtx responseTy
      [EffectAtom.free interface] resultTy resultEffect) :
    HasComp sig ctx
      (evalCtx.plug (.freeOp interface operation parameter))
      resultTy resultEffect :=
  contextTyping.plugTyping (.freeOp lookup parameterTyping)

end EffectSemantics
