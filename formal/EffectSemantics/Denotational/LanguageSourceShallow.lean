import EffectSemantics.Denotational.LanguageTypedShallow

namespace EffectSemantics

open EffectLanguage

/-- The matching source reduct denotes clause execution followed by the bare
captured continuation.  In particular, the shallow handler is not reinstalled
around that continuation. -/
noncomputable def ProducesLanguageWriterTree.answerWith
    {request : LanguageFreeRequest}
    (handlerTyping : HasLanguageAffineHandler sig [] request.interface handler replacement)
    (termTyping : HasLanguageComp sig [] request.source resultTy input)
    (found : handler.lookup request.operation = some clause)
    (clauseTree : LanguageWriterTree sig
      (LanguageClosedVal sig termTyping.exposedFreeView.responseTy))
    (clauseProduces : ProducesLanguageWriterTree sig
      (handlerTyping.instantiate found termTyping.exposedFreeView.lookup
        termTyping.exposedFreeView.parameterTyping) clauseTree)
    (continuation : LanguageClosedVal sig
        termTyping.exposedFreeView.responseTy →
      LanguageWriterTree sig (LanguageClosedVal sig resultTy))
    (resumeProduces : ∀ response,
      ProducesLanguageWriterTree sig
        (termTyping.exposedFreeView.principal.resumeTyping response)
        (continuation response)) :
    ProducesLanguageWriterTree sig
      (handlerTyping.answerWithTyping termTyping rfl found)
      (clauseTree.bind continuation) := by
  let requestTyping := termTyping.exposedFreeView
  let factor := requestTyping.contextTyping.principalFactor
    (newHole := principal 1) requestTyping.requestBelowHole
  let instantiated := handlerTyping.instantiate found requestTyping.lookup
    requestTyping.parameterTyping
  let renamedContext := factor.typing.renamePreserved
    (LanguageRenPreserves.shift [] requestTyping.responseTy)
  let continuationTyping : HasLanguageComp sig
      [requestTyping.responseTy] request.openResume resultTy factor.suffix := by
    have opened := renamedContext.plugTyping
      (HasLanguageComp.ret (HasLanguageVal.var (index := 0) rfl))
    rw [EffectLanguage.seq_one_left] at opened
    exact opened
  have bodyProduces : ∀ response : LanguageClosedVal sig requestTyping.responseTy,
      ProducesLanguageWriterTree sig
        (continuationTyping.subst0_preserved response.typing)
        (continuation response) := by
    intro response
    let resumedTyping : HasLanguageComp sig []
        (request.resume response.value) resultTy factor.suffix := by
      have resumed := factor.typing.plugTyping (HasLanguageComp.ret response.typing)
      rw [EffectLanguage.seq_one_left] at resumed
      exact resumed
    have resumedProduces : ProducesLanguageWriterTree sig resumedTyping
        (continuation response) :=
      ProducesLanguageWriterTree.rederive (resumeProduces response)
    apply ProducesLanguageWriterTree.retarget
      (typing₂ := continuationTyping.subst0_preserved response.typing)
      (LanguageFreeRequest.openResume_subst0 request response.value).symm
    exact resumedProduces
  let reductProduces := ProducesLanguageWriterTree.letE
    (boundTyping := instantiated) (bodyTyping := continuationTyping)
    clauseProduces continuation bodyProduces
  apply ProducesLanguageWriterTree.rederive
  exact ProducesLanguageWriterTree.weaken reductProduces
    (EffectLanguage.seq_replacement_le_handleWith factor.bound)

end EffectSemantics
