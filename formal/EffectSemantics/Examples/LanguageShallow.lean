import EffectSemantics.Metatheory.LanguageHandlerPreservation
import EffectSemantics.Examples.LanguageRecursion

namespace EffectSemantics

open EffectLanguage

def pureUnitLanguageHandler : LanguageAffineHandler :=
  ⟨[(0, .ret .unit)]⟩

theorem pureUnitLanguageHandler_lookup :
    pureUnitLanguageHandler.lookup 0 = some (.ret .unit) := by
  simp [pureUnitLanguageHandler, LanguageAffineHandler.lookup]

def pureUnitLanguageHandlerTyping :
    HasLanguageAffineHandler unitFreeLanguageSignature [] 0
      pureUnitLanguageHandler (principal 1) where
  clauseTyping := by
    intro operation clause found
    simp [pureUnitLanguageHandler, LanguageAffineHandler.lookup] at found
    rcases found with ⟨operationEq, clauseEq⟩
    subst operation
    subst clause
    exact ⟨.unit, .unit, unitFreeLanguageSignature_lookup, .ret .unit⟩

def bareLanguageRequest : LanguageFreeRequest :=
  ⟨0, 0, .unit, []⟩

def bareLanguageRequestTyping :
    HasLanguageComp unitFreeLanguageSignature [] bareLanguageRequest.source
      .unit (principal [loopAtom]) :=
  .freeOp unitFreeLanguageSignature_lookup .unit

def bareLanguageRequestAnswerTyping :
    HasLanguageComp unitFreeLanguageSignature []
      (bareLanguageRequest.answerWith (.ret .unit)) .unit
      (handleWith 0 (principal 1) (principal [loopAtom])) :=
  pureUnitLanguageHandlerTyping.answerWithTyping bareLanguageRequestTyping
    rfl pureUnitLanguageHandler_lookup

/-- In this exact singleton case the selected interface is genuinely removed
from the static grade, not merely hidden behind an abstract transformer. -/
def bareLanguageRequestAnswerPureTyping :
    HasLanguageComp unitFreeLanguageSignature []
      (bareLanguageRequest.answerWith (.ret .unit)) .unit (principal 1) := by
  rw [← EffectLanguage.handleWith_pure_singleton 0]
  exact bareLanguageRequestAnswerTyping

def bareLanguageRequestStep :
    LanguageShallowStep
      (.shallow 0 pureUnitLanguageHandler bareLanguageRequest.source)
      (.core (bareLanguageRequest.answerWith (.ret .unit))) :=
  .matched bareLanguageRequest rfl rfl pureUnitLanguageHandler_lookup

/-- End-to-end state preservation for a concrete matching shallow step. -/
def bareLanguageRequestStatePreserved :
    HasLanguageHandlerState unitFreeLanguageSignature [] 0
      pureUnitLanguageHandler (principal 1) (principal [loopAtom]) .unit
      (.core (bareLanguageRequest.answerWith (.ret .unit))) :=
  bareLanguageRequestStep.preserve pureUnitLanguageHandlerTyping
    (.shallow bareLanguageRequestTyping)

end EffectSemantics
