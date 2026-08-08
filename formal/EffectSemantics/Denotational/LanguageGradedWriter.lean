import EffectSemantics.Denotational.EffectLanguage
import EffectSemantics.Denotational.GradedWriterTree

namespace EffectSemantics.TypedWriterTree

open EffectLanguage

/-- The response-typed Writer/free carrier graded directly by downward-closed
trace languages. -/
inductive HasLanguageEffect :
    TypedWriterTree sig α → EffectLanguage → Type where
  | ret : HasLanguageEffect (.ret value) (principal 1)
  | tell : HasLanguageEffect tree language →
      HasLanguageEffect (.tell message tree)
        (seq (principal [EffectAtom.base 0]) language)
  | free : (∀ response, HasLanguageEffect (continuation response) language) →
      HasLanguageEffect (.free interface operation lookup parameter continuation)
        (seq (principal [EffectAtom.free interface]) language)
  | subeffect : HasLanguageEffect tree lower → lower ≤ upper →
      HasLanguageEffect tree upper

def HasLanguageEffect.weaken
    (typing : HasLanguageEffect tree lower) (bound : lower ≤ upper) :
    HasLanguageEffect tree upper := .subeffect typing bound

noncomputable def HasLanguageEffect.bind
    (treeTyping : HasLanguageEffect tree language)
    (nextTyping : ∀ value, HasLanguageEffect (next value) nextLanguage) :
    HasLanguageEffect (tree.bind next) (seq language nextLanguage) := by
  induction treeTyping with
  | ret =>
      rw [EffectLanguage.seq_one_left]
      exact nextTyping _
  | tell tailTyping ih =>
      rw [EffectLanguage.seq_assoc]
      exact HasLanguageEffect.tell ih
  | free continuationTyping ih =>
      rw [EffectLanguage.seq_assoc]
      exact HasLanguageEffect.free ih
  | subeffect inner bound ih =>
      exact ih.weaken (EffectLanguage.seq_mono bound
        (EffectLanguage.le_refl nextLanguage))

noncomputable def HasLanguageEffect.map
    {sig : Signature} {α β : Type} {tree : TypedWriterTree sig α}
    {language : EffectLanguage}
    (treeTyping : HasLanguageEffect tree language) (function : α → β) :
    HasLanguageEffect (TypedWriterTree.map function tree) language := by
  change HasLanguageEffect
    (tree.bind (fun value => .ret (function value))) language
  have mapped : HasLanguageEffect
      (tree.bind (fun value => TypedWriterTree.ret (function value)))
      (seq language (principal 1)) := treeTyping.bind
    (next := fun value => TypedWriterTree.ret (function value))
    (nextLanguage := EffectLanguage.principal 1)
    (fun value => @HasLanguageEffect.ret sig β (function value))
  rw [EffectLanguage.seq_one_right] at mapped
  exact mapped

/-- Every observed Writer trace belongs to the declared trace language. -/
theorem HasLanguageEffect.observationMember
    (typing : HasLanguageEffect tree language)
    (observes : Observes tree log value) :
    language.contains (WriterTree.writerTrace log) := by
  induction typing generalizing log value with
  | ret =>
      cases observes
      exact Effect.le_refl 1
  | tell tailTyping ih =>
      cases observes with
      | tell tailObserved =>
          let tailMember := ih tailObserved
          exact ⟨[EffectAtom.base 0], WriterTree.writerTrace _,
            Effect.le_refl _, tailMember, Effect.le_refl _⟩
  | free continuationTyping ih => cases observes
  | subeffect inner bound ih => exact bound _ (ih observes)

end EffectSemantics.TypedWriterTree
