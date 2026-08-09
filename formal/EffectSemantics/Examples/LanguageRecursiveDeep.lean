import EffectSemantics.Examples.LanguageShallow
import EffectSemantics.Certificate.LanguageRecursive

namespace EffectSemantics

open EffectLanguage

def pureUnitRecLanguageHandler : LanguageAffineHandler .recursive :=
  ⟨[(0, .ret .unit)]⟩

theorem pureUnitRecLanguageHandler_lookup :
    pureUnitRecLanguageHandler.lookup 0 = some (.ret .unit) := by
  simp [pureUnitRecLanguageHandler, LanguageAffineHandler.lookup]

def bareRecLanguageRequest : RecLanguageFreeRequest :=
  ⟨0, 0, .unit, []⟩

/-- A single selected request is handled by one shallow match; the recursive
deep semantics then reaches Unit. -/
theorem bareLanguageDeepRun :
    LanguageDeepWriterRuns 0 pureUnitRecLanguageHandler
      bareRecLanguageRequest.source [] .unit := by
  apply LanguageDeepWriterRuns.matched bareRecLanguageRequest rfl rfl
    pureUnitRecLanguageHandler_lookup
  apply LanguageDeepWriterRuns.internal LanguageStep.letReturn
  exact LanguageDeepWriterRuns.returned

theorem bareLanguageDeepDenotation :
    languageDeepWriterSemantics 0 pureUnitRecLanguageHandler
      bareRecLanguageRequest.source = some ([], .unit) :=
  language_deep_writer_semantic_adequacy.mp bareLanguageDeepRun

/-- The false branch of the recursive conditional unfolds once and returns;
this exercises actual `fixBeta` in the completed deep semantics. -/
def runConditionalFalse : RecLanguageComp :=
  .app (.fixLam .recursive .bool loopLanguage conditionalLoopBody) (.bool false)

def runConditionalFalseTyping :
    HasLanguageComp unitFreeLanguageSignature [] runConditionalFalse
      .unit loopLanguage :=
  .app (.fixLam .recursive conditionalLoopBodyTyping) (.bool (value := false))

theorem runConditionalFalseDeepRun :
    LanguageDeepWriterRuns 0 pureUnitRecLanguageHandler
      runConditionalFalse [] .unit := by
  apply LanguageDeepWriterRuns.internal LanguageStep.fixBeta
  apply LanguageDeepWriterRuns.internal LanguageStep.ifFalse
  exact LanguageDeepWriterRuns.returned

theorem runConditionalFalseDenotation :
    languageDeepWriterSemantics 0 pureUnitRecLanguageHandler
      runConditionalFalse = some ([], .unit) :=
  language_deep_writer_semantic_adequacy.mp runConditionalFalseDeepRun

end EffectSemantics
