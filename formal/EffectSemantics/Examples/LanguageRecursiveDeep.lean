import EffectSemantics.Examples.LanguageShallow
import EffectSemantics.Certificate.LanguageRecursive

namespace EffectSemantics

open EffectLanguage

theorem unitFreeLanguageWriterResponse :
    LanguageWriterResponseUnit unitFreeLanguageSignature where
  responseUnit := by
    intro parameterTy responseTy impossible
    simp [unitFreeLanguageSignature] at impossible

/-- The concrete language signature and pure unit handler instantiate the
entire recursive structure-preservation certificate. -/
noncomputable def unitFreeLanguageRecursiveCert :
    LanguageRecursiveStructureCert unitFreeLanguageSignature 0
      pureUnitLanguageHandler (principal 1) :=
  languageRecursiveStructurePreservation unitFreeLanguageWriterResponse
    pureUnitLanguageHandlerTyping

/-- A single selected request is handled by one shallow match; the recursive
deep semantics then reaches Unit. -/
theorem bareLanguageDeepRun :
    LanguageDeepWriterRuns 0 pureUnitLanguageHandler
      bareLanguageRequest.source [] .unit := by
  apply LanguageDeepWriterRuns.matched bareLanguageRequest rfl rfl
    pureUnitLanguageHandler_lookup
  apply LanguageDeepWriterRuns.internal LanguageStep.letReturn
  exact LanguageDeepWriterRuns.returned

theorem bareLanguageDeepDenotation :
    languageDeepWriterSemantics 0 pureUnitLanguageHandler
      bareLanguageRequest.source = some ([], .unit) :=
  language_deep_writer_semantic_adequacy.mp bareLanguageDeepRun

/-- The false branch of the recursive conditional unfolds once and returns;
this exercises actual `fixBeta` in the completed deep semantics. -/
def runConditionalFalse : LanguageComp :=
  .app (.fixLam .bool loopLanguage conditionalLoopBody) (.bool false)

def runConditionalFalseTyping :
    HasLanguageComp unitFreeLanguageSignature [] runConditionalFalse
      .unit loopLanguage :=
  .app (.fixLam conditionalLoopBodyTyping) (.bool (value := false))

theorem runConditionalFalseDeepRun :
    LanguageDeepWriterRuns 0 pureUnitLanguageHandler
      runConditionalFalse [] .unit := by
  apply LanguageDeepWriterRuns.internal LanguageStep.fixBeta
  apply LanguageDeepWriterRuns.internal LanguageStep.ifFalse
  exact LanguageDeepWriterRuns.returned

theorem runConditionalFalseDenotation :
    languageDeepWriterSemantics 0 pureUnitLanguageHandler
      runConditionalFalse = some ([], .unit) :=
  language_deep_writer_semantic_adequacy.mp runConditionalFalseDeepRun

theorem runConditionalFalseResultTyped :
    Nonempty (HasLanguageVal unitFreeLanguageSignature [] (.unit : LanguageVal)
      .unit) :=
  unitFreeLanguageRecursiveCert.fundamental runConditionalFalseTyping
    runConditionalFalseDenotation

end EffectSemantics
