import EffectSemantics.Metatheory.LanguageHandlerPreservation

namespace EffectSemantics

inductive LanguageShallowProgress : LanguageHandlerState → Type where
  | step : LanguageShallowStep state next → LanguageShallowProgress state
  | boundary : LanguageShallowBoundary state → LanguageShallowProgress state

/-- A running shallow handler either takes an internal/return/matching step or
exposes exactly one forwarded base/free boundary.  Unrelated interfaces keep
the handler installed until a selected request is reached. -/
def HasLanguageHandlerState.progressClosed
    (typing : HasLanguageHandlerState sig [] interface handler
      replacement input resultTy (.shallow interface handler term)) :
    LanguageShallowProgress (.shallow interface handler term) := by
  cases typing with
  | shallow termTyping =>
      exact match termTyping.progressClosed with
      | .returned =>
          LanguageShallowProgress.step LanguageShallowStep.returned
      | .internal step =>
          LanguageShallowProgress.step (LanguageShallowStep.internal step)
      | .boundary boundary =>
          match boundary.view with
          | .base request =>
              LanguageShallowProgress.boundary
                (LanguageShallowBoundary.base request)
          | .free request =>
              if same : request.interface = interface then
                match found : handler.lookup request.operation with
                | some clause => LanguageShallowProgress.step
                    (.matched request rfl same found)
                | none => LanguageShallowProgress.boundary
                    (.freeMissing request same found)
              else LanguageShallowProgress.boundary
                (.freeOther request same)

end EffectSemantics
