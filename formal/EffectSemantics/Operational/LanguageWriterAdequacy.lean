import EffectSemantics.Operational.LanguageWriterEvaluation

namespace EffectSemantics

open EffectLanguage

inductive LanguageWriterRuns (sig : LanguageSignature) :
    {term : LanguageComp} → {resultTy : LanguageTy} →
    {effect : EffectLanguage} →
    (typing : HasLanguageComp sig [] term resultTy effect) →
    List LanguageVal → LanguageClosedVal sig resultTy → Type where
  | returned (typing : HasLanguageComp sig [] (.ret value) resultTy effect) :
      LanguageWriterRuns sig typing [] ⟨value, typing.returnView.valueTyping⟩
  | internal (step : LanguageStep term next)
      (runs : LanguageWriterRuns sig (step.preserve typing) log value) :
      LanguageWriterRuns sig typing log value
  | rederive {typing₁ typing₂ : HasLanguageComp sig [] term resultTy effect}
      (runs : LanguageWriterRuns sig typing₁ log value) :
      LanguageWriterRuns sig typing₂ log value
  | retarget
      {typing₁ : HasLanguageComp sig [] term₁ resultTy effect}
      {typing₂ : HasLanguageComp sig [] term₂ resultTy effect}
      (equal : term₁ = term₂) (runs : LanguageWriterRuns sig typing₁ log value) :
      LanguageWriterRuns sig typing₂ log value
  | weaken {typing : HasLanguageComp sig [] term resultTy lower}
      (runs : LanguageWriterRuns sig typing log value) (bound : lower ≤ upper) :
      LanguageWriterRuns sig (typing.subeffect bound) log value
  | tell {request : LanguageBaseRequest} {parameterTy : LanguageTy}
      (typing : HasLanguageComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (lookup : sig.base request.operation = some ⟨parameterTy, .unit⟩)
      (parameterTyping : HasLanguageVal sig [] request.parameter parameterTy)
      {suffix : EffectLanguage}
      (resumeTyping : HasLanguageComp sig [] (request.resume .unit) resultTy suffix)
      (bound : EffectLanguage.seq (principal [EffectAtom.base 0]) suffix ≤
        resultEffect)
      (runs : LanguageWriterRuns sig resumeTyping log value) :
      LanguageWriterRuns sig typing (request.parameter :: log) value

noncomputable def ProducesLanguageWriterTree.sound
    (produces : ProducesLanguageWriterTree sig typing tree)
    (observes : LanguageWriterTree.Observes tree log value) :
    LanguageWriterRuns sig typing log value := by
  induction produces generalizing log with
  | returned typing =>
      cases observes
      exact .returned typing
  | internal step produces ih => exact .internal step (ih observes)
  | rederive produces ih => exact .rederive (ih observes)
  | retarget equal produces ih => exact .retarget equal (ih observes)
  | weaken produces bound ih => exact .weaken (ih observes) bound
  | tell typing selected lookup parameterTyping resumeTyping bound produces ih =>
      cases observes with
      | tell tailObserved =>
          exact .tell typing selected lookup parameterTyping resumeTyping bound
            (ih tailObserved)
  | free typing lookup parameterTyping continuation resumeTyping bound produces ih =>
      cases observes

noncomputable def LanguageWriterRuns.complete
    (runs : LanguageWriterRuns sig typing log value) :
    Σ tree, ProducesLanguageWriterTree sig typing tree ×
      LanguageWriterTree.Observes tree log value := by
  induction runs with
  | returned typing =>
      exact ⟨.ret ⟨_, typing.returnView.valueTyping⟩, .returned typing, .ret⟩
  | internal step runs ih =>
      exact ⟨ih.1, .internal step ih.2.1, ih.2.2⟩
  | rederive runs ih => exact ⟨ih.1, .rederive ih.2.1, ih.2.2⟩
  | retarget equal runs ih =>
      exact ⟨ih.1, .retarget equal ih.2.1, ih.2.2⟩
  | weaken runs bound ih =>
      exact ⟨ih.1, .weaken ih.2.1 bound, ih.2.2⟩
  | tell typing selected lookup parameterTyping resumeTyping bound runs ih =>
      exact ⟨.tell _ ih.1,
        .tell typing selected lookup parameterTyping resumeTyping bound ih.2.1,
        .tell ih.2.2⟩

theorem language_writer_operational_tree_adequacy :
    Nonempty (LanguageWriterRuns sig typing log value) ↔
      Nonempty (Σ tree, ProducesLanguageWriterTree sig typing tree ×
        LanguageWriterTree.Observes tree log value) := by
  constructor
  · rintro ⟨runs⟩
    exact ⟨runs.complete⟩
  · rintro ⟨tree, produces, observes⟩
    exact ⟨produces.sound observes⟩

end EffectSemantics
