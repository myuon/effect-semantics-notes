import EffectSemantics.Metatheory.LanguageHandlerTyping

namespace EffectSemantics

open EffectLanguage

/-- Typing invariant for a running shallow handler.  Before it fires the
source retains `input`; after return or a match the state has the transformed
first-occurrence language. -/
inductive HasLanguageHandlerState
    (sig : LanguageSignature) (ctx : LanguageContext)
    (interface : Nat) (handler : LanguageAffineHandler)
    (replacement input : EffectLanguage) (resultTy : LanguageTy) :
    LanguageHandlerState → Type where
  | shallow : ctx ⊢[sig] term : resultTy ! input →
      HasLanguageHandlerState sig ctx interface handler replacement input resultTy
        (.shallow interface handler term)
  | core : ctx ⊢[sig] term : resultTy !
      handleWith interface replacement input →
      HasLanguageHandlerState sig ctx interface handler replacement input resultTy
        (.core term)

/-- Every internal/return/matching transition preserves the handler-state
typing invariant. -/
def LanguageShallowStep.preserve
    (handlerTyping : HasLanguageAffineHandler sig ctx interface handler replacement)
    (step : LanguageShallowStep state next)
    (typing : HasLanguageHandlerState sig ctx interface handler
      replacement input resultTy state) :
    HasLanguageHandlerState sig ctx interface handler
      replacement input resultTy next := by
  cases typing with
  | core coreTyping => cases step
  | shallow termTyping =>
      cases step with
      | internal inner => exact .shallow (inner.preserve termTyping)
      | returned =>
          let view := termTyping.returnView
          exact .core (.subeffect (.ret view.valueTyping)
            (EffectLanguage.pure_le_handleWith view.pureBelow))
      | matched request exposed same found =>
          subst exposed
          exact .core (handlerTyping.answerWithTyping termTyping same found)

/-- Forwarding an unrelated or missing free request and receiving a
well-typed response reinstalls the same shallow handler at the unchanged input
grade. -/
def HasLanguageHandlerState.resumeFree
    {request : LanguageFreeRequest}
    (termTyping : ctx ⊢[sig] request.source : resultTy ! input)
    (responseTyping : ctx ⊢[sig] response :ᵥ
      termTyping.exposedFreeView.responseTy) :
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy
      (.shallow interface handler (request.resume response)) :=
  .shallow (termTyping.exposedFreeView.resumeTyping responseTyping)

/-- The same preservation fact for an outward base-effect request. -/
def HasLanguageHandlerState.resumeBase
    {request : LanguageBaseRequest}
    (termTyping : ctx ⊢[sig] request.source : resultTy ! input)
    (responseTyping : ctx ⊢[sig] response :ᵥ
      termTyping.exposedBaseView.responseTy) :
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy
      (.shallow interface handler (request.resume response)) :=
  .shallow (termTyping.exposedBaseView.resumeTyping responseTyping)

end EffectSemantics
