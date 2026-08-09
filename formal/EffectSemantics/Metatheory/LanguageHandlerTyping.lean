import EffectSemantics.Operational.LanguageShallowHandler

namespace EffectSemantics

open EffectLanguage

def HasLanguageEvalContext.renamePreserved
    (typing : HasLanguageEvalContext sig source evalCtx holeTy holeEffect
      resultTy resultEffect)
    (preserves : LanguageRenPreserves source target rename) :
    HasLanguageEvalContext sig target
      (LanguageEvalContext.rename rename evalCtx) holeTy holeEffect
      resultTy resultEffect :=
  match typing with
  | .hole => .hole
  | .letE bodyTyping frameBound restTyping =>
      .letE (bodyTyping.rename_preserved (preserves.lift _)) frameBound
        (restTyping.renamePreserved preserves)

structure TypedLanguageAffineClause (sig : LanguageSignature)
    (ctx : LanguageContext) (interface operation : Nat)
    (clause : LanguageComp) (clauseEffect : EffectLanguage) where
  parameterTy : LanguageTy
  responseTy : LanguageTy
  signatureLookup : sig.free interface operation =
    some ⟨parameterTy, responseTy⟩
  bodyTyping : HasLanguageComp sig (parameterTy :: ctx)
    clause responseTy clauseEffect

structure HasLanguageAffineHandler (sig : LanguageSignature)
    (ctx : LanguageContext) (interface : Nat)
    (handler : LanguageAffineHandler) (clauseEffect : EffectLanguage) where
  clauseTyping : ∀ {operation clause},
    handler.lookup operation = some clause →
    TypedLanguageAffineClause sig ctx interface operation clause clauseEffect

def HasLanguageAffineHandler.instantiate
    (typing : HasLanguageAffineHandler sig ctx interface handler clauseEffect)
    (found : handler.lookup operation = some clause)
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (parameterTyping : HasLanguageVal sig ctx parameter parameterTy) :
    HasLanguageComp sig ctx (clause.subst0 parameter) responseTy clauseEffect := by
  let typed := typing.clauseTyping found
  have signatureEq :
      LanguageOpDecl.mk typed.parameterTy typed.responseTy =
        LanguageOpDecl.mk parameterTy responseTy :=
    Option.some.inj (typed.signatureLookup.symm.trans lookup)
  cases signatureEq
  exact typed.bodyTyping.subst0_preserved parameterTyping

/-- The matching reduct receives the precise first-occurrence transformed
language, even when the clause itself has a non-principal regular effect. -/
def HasLanguageAffineHandler.answerWithTyping
    {request : LanguageFreeRequest}
    (handlerTyping : HasLanguageAffineHandler sig ctx interface handler replacement)
    (termTyping : HasLanguageComp sig ctx request.source resultTy input)
    (same : request.interface = interface)
    (found : handler.lookup request.operation = some clause) :
    HasLanguageComp sig ctx (request.answerWith clause) resultTy
      (handleWith interface replacement input) := by
  let requestTyping := termTyping.exposedFreeView
  subst interface
  let factor := requestTyping.contextTyping.principalFactor
    (newHole := principal 1) requestTyping.requestBelowHole
  let clauseTyping := handlerTyping.instantiate found requestTyping.lookup
    requestTyping.parameterTyping
  let renamedContext := factor.typing.renamePreserved
    (LanguageRenPreserves.shift ctx requestTyping.responseTy)
  let continuationTyping : HasLanguageComp sig
      (requestTyping.responseTy :: ctx) request.openResume resultTy factor.suffix := by
    have opened := renamedContext.plugTyping
      (HasLanguageComp.ret (HasLanguageVal.var (index := 0) rfl))
    rw [EffectLanguage.seq_one_left] at opened
    exact opened
  let reductTyping : HasLanguageComp sig ctx
      (request.answerWith clause) resultTy
      (EffectLanguage.seq replacement factor.suffix) :=
    .letE clauseTyping continuationTyping
  exact .subeffect reductTyping
    (EffectLanguage.seq_replacement_le_handleWith factor.bound)

end EffectSemantics
