import EffectSemantics.Metatheory.LanguageProgress

namespace EffectSemantics

open EffectLanguage

def erasingSignature : LanguageSignature where
  base _ := none
  free
    | 0, 0 => some ⟨.unit, .arr .unit bottom .unit⟩
    | _, _ => none

/-- The request happens before an application whose latent language is empty.
Sequential composition therefore erases the visible request from the final
annotation. -/
def erasingFreeTerm : LanguageComp :=
  .letE (.freeOp 0 0 .unit) (.app (.var 0) .unit)

def erasingFreeTerm_typed_bottom :
    HasLanguageComp erasingSignature [] erasingFreeTerm .unit bottom := by
  have request : HasLanguageComp erasingSignature []
      (.freeOp 0 0 .unit) (.arr .unit bottom .unit)
      (principal [EffectAtom.free 0]) :=
    .freeOp rfl .unit
  have continuation : HasLanguageComp erasingSignature
      [.arr .unit bottom .unit] (.app (.var 0) .unit) .unit bottom :=
    .app (.var rfl) .unit
  have combined := HasLanguageComp.letE request continuation
  simpa [erasingFreeTerm, EffectLanguage.seq_right_bottom] using combined

def erasingFreeTerm_exposes_request : LanguageBoundary erasingFreeTerm :=
  .underLet .free

/-- Unconditional "an effect with no free atom cannot expose a free request"
is false for the current language algebra and typing rules. -/
theorem empty_free_effect_safety_counterexample :
    Nonempty (HasLanguageComp erasingSignature [] erasingFreeTerm .unit bottom) ∧
    Nonempty (LanguageBoundary erasingFreeTerm) ∧
    (∀ trace, ¬ bottom.contains trace) := by
  exact ⟨⟨erasingFreeTerm_typed_bottom⟩, ⟨erasingFreeTerm_exposes_request⟩,
    fun _ member => member⟩

end EffectSemantics
