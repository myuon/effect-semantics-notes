import EffectSemantics.Metatheory.LanguageRequests

namespace EffectSemantics

structure LanguageAffineHandler where
  clauses : List (Nat × LanguageComp)

def LanguageAffineHandler.lookup (handler : LanguageAffineHandler)
    (operation : Nat) : Option LanguageComp :=
  (handler.clauses.find? (fun clause => clause.1 = operation)).map Prod.snd

def LanguageFreeRequest.answerWith
    (request : LanguageFreeRequest) (clause : LanguageComp) : LanguageComp :=
  .letE (clause.subst0 request.parameter) request.openResume

inductive LanguageHandlerState where
  | core (term : LanguageComp)
  | shallow (interface : Nat) (handler : LanguageAffineHandler)
      (term : LanguageComp)

inductive LanguageShallowStep :
    LanguageHandlerState → LanguageHandlerState → Type where
  | internal : LanguageStep term next →
      LanguageShallowStep (.shallow interface handler term)
        (.shallow interface handler next)
  | returned :
      LanguageShallowStep (.shallow interface handler (.ret value))
        (.core (.ret value))
  | matched (request : LanguageFreeRequest) :
      request.source = term → request.interface = interface →
      handler.lookup request.operation = some clause →
      LanguageShallowStep (.shallow interface handler term)
        (.core (request.answerWith clause))

/-- Unrelated requests are forwarded while the same shallow handler remains
installed around the resumed continuation; selected requests are caught only
when their clause exists. -/
inductive LanguageShallowBoundary : LanguageHandlerState → Type where
  | base (request : LanguageBaseRequest) :
      LanguageShallowBoundary (.shallow interface handler request.source)
  | freeOther (request : LanguageFreeRequest)
      (different : request.interface ≠ interface) :
      LanguageShallowBoundary (.shallow interface handler request.source)
  | freeMissing (request : LanguageFreeRequest)
      (same : request.interface = interface)
      (missing : handler.lookup request.operation = none) :
      LanguageShallowBoundary (.shallow interface handler request.source)

def LanguageShallowBoundary.resume :
    LanguageShallowBoundary (.shallow interface handler term) →
      LanguageVal → LanguageHandlerState
  | .base request, response =>
      .shallow interface handler (request.resume response)
  | .freeOther request _, response =>
      .shallow interface handler (request.resume response)
  | .freeMissing request _ _, response =>
      .shallow interface handler (request.resume response)

end EffectSemantics
