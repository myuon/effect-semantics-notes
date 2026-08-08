import EffectSemantics.Recursive.DeepWriterLogicalRelation
import EffectSemantics.Syntax.HandlerTyping

namespace EffectSemantics

/-- The only base operation consumed by the closed Writer observer returns
unit.  Its parameter type is deliberately left abstract. -/
def WriterResponseUnit (sig : Signature) : Prop :=
  ∀ parameterTy responseTy,
    sig.base 0 = some ⟨parameterTy, responseTy⟩ → responseTy = .unit

/-- Terminating recursive deep Writer handling preserves the source result
type.  Intermediate effect bounds may change when a clause is installed, so
the induction quantifies over them rather than pretending that deep handling
has an exact old grade. -/
theorem DeepWriterRuns.resultTyped
    (runs : DeepWriterRuns interface handler term log value)
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig) :
    Nonempty (HasVal sig [] value resultTy) := by
  induction runs generalizing effect with
  | returned => exact ⟨typing.returnView.valueTyping⟩
  | internal step runs ih =>
      exact ih (step.preserve typing)
  | tell exposed selected runs ih =>
      rw [exposed] at typing
      let requestTyping := typing.exposedBaseView
      have responseEq : requestTyping.responseTy = .unit := by
        apply writerUnit requestTyping.parameterTy requestTyping.responseTy
        simpa [selected] using requestTyping.lookup
      have unitTyping : HasVal sig [] .unit requestTyping.responseTy := by
        rw [responseEq]
        exact .unit
      exact ih (requestTyping.resumeTyping unitTyping)
  | matched exposed same found runs ih =>
      rw [exposed] at typing
      exact ih (handlerTyping.answerWithTyping typing same found)

theorem deepWriterLimit_result_typed
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig)
    (observed : term.deepWriterLimit interface handler = some (log, value)) :
    Nonempty (HasVal sig [] value resultTy) :=
  (deep_writer_limit_adequacy.mpr observed).resultTyped
    typing handlerTyping writerUnit

/-- The admissible-pole proof also has a typed instance: every finite result
of the recursive limit is a closed value of the source computation's result
type. -/
theorem deepWriterLimit_typedPole
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig) :
    DeepWriterSatisfies
      (fun term _log value => ∀ resultTy effect,
        HasComp sig [] term resultTy effect →
          Nonempty (HasVal sig [] value resultTy))
      (deepWriterLimitFamily interface handler) := by
  intro term log value observed resultTy effect typing
  exact deepWriterLimit_result_typed typing handlerTyping writerUnit observed

end EffectSemantics
