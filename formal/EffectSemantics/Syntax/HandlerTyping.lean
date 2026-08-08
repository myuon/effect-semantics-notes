import EffectSemantics.Operational.ShallowHandler
import EffectSemantics.Metatheory.RequestDecomposition

namespace EffectSemantics

def HasEvalContext.renamePreserved
    {sig : Signature} {source target : Context} {rename : Nat → Nat}
    {evalCtx : EvalContext} {holeTy resultTy : Ty}
    {holeEffect resultEffect : Effect}
    (typing : HasEvalContext sig source evalCtx holeTy holeEffect
      resultTy resultEffect)
    (preserves : RenPreserves source target rename) :
    HasEvalContext sig target (evalCtx.rename rename) holeTy holeEffect
      resultTy resultEffect :=
  match typing with
  | .hole => .hole
  | .letE bodyTyping frameBound restTyping =>
      .letE (bodyTyping.rename_preserved (preserves.lift _)) frameBound
        (restTyping.renamePreserved preserves)

/-- Local typing evidence for one affine operation clause. -/
structure TypedAffineClause (sig : Signature) (ctx : Context)
    (interface operation : Nat) (clause : Comp) (clauseEffect : Effect) where
  parameterTy : Ty
  responseTy : Ty
  signatureLookup : sig.free interface operation =
    some ⟨parameterTy, responseTy⟩
  bodyTyping : HasComp sig (parameterTy :: ctx) clause responseTy clauseEffect

/-- The syntactic part of the affine handler certificate.  It deliberately
does not yet claim an output-grade transformation: that requires the ordered
optionality and residual-context obligations isolated in Chapter III. -/
structure HasAffineHandler (sig : Signature) (ctx : Context)
    (interface : Nat) (handler : AffineHandler) (clauseEffect : Effect) where
  clauseTyping : ∀ {operation clause},
    handler.lookup operation = some clause →
    TypedAffineClause sig ctx interface operation clause clauseEffect

/-- Exhaustiveness is separate from ordinary handler typing.  Partial
handlers remain meaningful because missing clauses are transparently
forwarded. -/
def AffineHandler.Exhaustive (sig : Signature) (interface : Nat)
    (handler : AffineHandler) : Prop :=
  ∀ operation parameterTy responseTy,
    sig.free interface operation = some ⟨parameterTy, responseTy⟩ →
    ∃ clause, handler.lookup operation = some clause

def HasAffineHandler.typedClause
    (typing : HasAffineHandler sig ctx interface handler clauseEffect)
    (found : handler.lookup operation = some clause) :
    TypedAffineClause sig ctx interface operation clause clauseEffect :=
  typing.clauseTyping found

/-- Substituting the runtime operation parameter into a typed affine clause
produces a response computation in the surrounding context. -/
def HasAffineHandler.instantiate
    (typing : HasAffineHandler sig ctx interface handler clauseEffect)
    (found : handler.lookup operation = some clause)
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (parameterTyping : HasVal sig ctx parameter parameterTy) :
    HasComp sig ctx (clause.subst0 parameter) responseTy clauseEffect := by
  let typed := typing.typedClause found
  have signatureEq :
      OpDecl.mk typed.parameterTy typed.responseTy =
        OpDecl.mk parameterTy responseTy := by
    exact Option.some.inj (typed.signatureLookup.symm.trans lookup)
  cases signatureEq
  exact typed.bodyTyping.subst0_preserved parameterTyping

/-- The bare captured continuation is typable under a fresh response binder.
The optionality premise is precisely what permits replacing the operation hole
by a pure return while retaining the declared context bound. -/
def TypedFreeRequest.openResumeTyping
    (requestTyping : TypedFreeRequest sig ctx request resultTy resultEffect)
    (optional : 1 ≤ requestTyping.holeEffect) :
    HasComp sig (requestTyping.responseTy :: ctx) request.openResume
      resultTy resultEffect := by
  let renamed := requestTyping.contextTyping.renamePreserved
    (RenPreserves.shift ctx requestTyping.responseTy)
  exact renamed.plugTyping
    ((HasComp.ret (HasVal.var rfl)).subeffect optional)

/-- Every typed free request has the optionality needed to resume it with a
value, because `1 ≤ [free interface]` and the request grade lies below the
effect accepted by its residual context. -/
def TypedFreeRequest.openResumeTypingDefault
    (requestTyping : TypedFreeRequest sig ctx request resultTy resultEffect) :
    HasComp sig (requestTyping.responseTy :: ctx) request.openResume
      resultTy resultEffect :=
  requestTyping.openResumeTyping
    (Effect.le_trans (Effect.optional_free request.interface)
      requestTyping.requestBelowHole)

/-- Coarse preservation for the affine matching reduct.  This deliberately
retains the whole old result bound; the sharper `b * clauseEffect * e` theorem
requires the principal prefix/suffix refinement developed next. -/
def HasAffineHandler.answerWithTyping
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect : Effect}
    {request : FreeRequest} {resultTy : Ty} {resultEffect : Effect}
    {clause : Comp}
    (handlerTyping : HasAffineHandler sig ctx interface handler clauseEffect)
    (termTyping : HasComp sig ctx request.source resultTy resultEffect)
    (same : request.interface = interface)
    (found : handler.lookup request.operation = some clause) :
    HasComp sig ctx (request.answerWith clause) resultTy
      (clauseEffect * resultEffect) := by
  let requestTyping := termTyping.exposedFreeView
  subst interface
  exact .letE
    (handlerTyping.instantiate found requestTyping.lookup
      requestTyping.parameterTyping)
    requestTyping.openResumeTypingDefault

/-- Sharp ordered preservation for a matching affine clause.  A selected
interface cannot be consumed inside the prefix because that prefix is
interface-free; consequently the principal residual suffix embeds in `post`.
The operational reduct is then typed at the advertised replacement word. -/
def HasAffineHandler.answerWithTypingSharp
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect pre post : Effect}
    {request : FreeRequest} {resultTy : Ty} {clause : Comp}
    (handlerTyping : HasAffineHandler sig ctx interface handler clauseEffect)
    (termTyping : HasComp sig ctx request.source resultTy
      (pre * [EffectAtom.free interface] * post))
    (same : request.interface = interface)
    (preFree : Effect.FreeOf interface pre)
    (found : handler.lookup request.operation = some clause) :
    HasComp sig ctx (request.answerWith clause) resultTy
      (pre * clauseEffect * post) := by
  let requestTyping := termTyping.exposedFreeView
  subst interface
  let factor := requestTyping.contextTyping.principalFactor
    (newHole := (1 : Effect)) requestTyping.requestBelowHole
  have suffixBelow : factor.suffix ≤ post := by
    apply Effect.cancel_first_free preFree
    have bound := factor.bound
    change List.Sublist ([EffectAtom.free request.interface] ++ factor.suffix)
      ((pre ++ [EffectAtom.free request.interface]) ++ post) at bound
    simpa only [List.singleton_append, List.append_assoc] using bound
  let clauseTyping := handlerTyping.instantiate found requestTyping.lookup
    requestTyping.parameterTyping
  let renamedContext := factor.typing.renamePreserved
    (RenPreserves.shift ctx requestTyping.responseTy)
  let continuationTyping : HasComp sig (requestTyping.responseTy :: ctx)
      request.openResume resultTy factor.suffix := by
    simpa [FreeRequest.openResume] using renamedContext.plugTyping
      (HasComp.ret (HasVal.var rfl))
  let reductTyping : HasComp sig ctx (request.answerWith clause) resultTy
      (clauseEffect * factor.suffix) := by
    exact .letE clauseTyping continuationTyping
  apply reductTyping.subeffect
  apply Effect.le_trans (Effect.le_seq (Effect.le_refl clauseEffect) suffixBelow)
  simpa only [Effect.mul_assoc] using
    Effect.le_left_padding pre (clauseEffect * post)

end EffectSemantics
