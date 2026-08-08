import EffectSemantics.Metatheory.Preservation

namespace EffectSemantics

structure SuffixFactor (pre result : Effect) where
  suffix : Effect
  bound : pre * suffix ≤ result

/-- Typing of an evaluation context from a hole computation to the final
computation. Frames are innermost first, matching `EvalContext.plug`. -/
inductive HasEvalContext (sig : Signature) (ctx : Context) :
    EvalContext → Ty → Effect → Ty → Effect → Type where
  | hole : HasEvalContext sig ctx [] holeTy holeEffect holeTy holeEffect
  | letE :
      HasComp sig (holeTy :: ctx) body frameTy bodyEffect →
      holeEffect * bodyEffect ≤ frameEffect →
      HasEvalContext sig ctx rest frameTy frameEffect
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
  | .letE bodyTyping bound restTyping =>
      restTyping.plugTyping ((HasComp.letE termTyping bodyTyping).subeffect bound)

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

/-- Every prefix already permitted at the hole remains in order in the final
context effect; frames only append effects and may weaken. -/
def HasEvalContext.factorSuffix
    {sig : Signature} {ctx : Context} {evalCtx : EvalContext}
    {holeTy resultTy : Ty} {holeEffect resultEffect pre : Effect}
    (contextTyping : HasEvalContext sig ctx evalCtx holeTy holeEffect
      resultTy resultEffect)
    (prefixBelow : pre ≤ holeEffect) :
    SuffixFactor pre resultEffect :=
  match contextTyping with
  | .hole => ⟨1, by simpa using prefixBelow⟩
  | .letE (bodyEffect := bodyEffect) bodyTyping frameBound restTyping =>
      let nextBelow : pre * bodyEffect ≤ _ :=
        Effect.le_trans (Effect.le_seq prefixBelow (Effect.le_refl bodyEffect)) frameBound
      let result := restTyping.factorSuffix nextBelow
      ⟨bodyEffect * result.suffix, by
        simpa only [Effect.mul_assoc] using result.bound⟩

end EffectSemantics
