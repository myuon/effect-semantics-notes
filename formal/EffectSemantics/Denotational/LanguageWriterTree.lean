import EffectSemantics.Metatheory.LanguageHandlerProgress

namespace EffectSemantics

open EffectLanguage

structure LanguageClosedVal (sig : LanguageSignature) (ty : LanguageTy) where
  value : LanguageVal
  typing : HasLanguageVal sig [] value ty

/-- Response-typed Writer/free behavior trees for the language-graded source. -/
inductive LanguageWriterTree (sig : LanguageSignature) (α : Type) where
  | ret (value : α)
  | tell (message : LanguageVal) (next : LanguageWriterTree sig α)
  | free (interface operation : Nat)
      {parameterTy responseTy : LanguageTy}
      (lookup : sig.free interface operation =
        some ⟨parameterTy, responseTy⟩)
      (parameter : LanguageClosedVal sig parameterTy)
      (continuation : LanguageClosedVal sig responseTy →
        LanguageWriterTree sig α)

namespace LanguageWriterTree

def bind (tree : LanguageWriterTree sig α)
    (next : α → LanguageWriterTree sig β) : LanguageWriterTree sig β :=
  match tree with
  | .ret value => next value
  | .tell message tail => .tell message (tail.bind next)
  | .free interface operation lookup parameter continuation =>
      .free interface operation lookup parameter
        (fun response => (continuation response).bind next)

def map (function : α → β) (tree : LanguageWriterTree sig α) :
    LanguageWriterTree sig β :=
  tree.bind (fun value => .ret (function value))

theorem bind_ret (tree : LanguageWriterTree sig α) :
    tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation lookup parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : LanguageWriterTree sig α)
    (first : α → LanguageWriterTree sig β)
    (second : β → LanguageWriterTree sig γ) :
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation lookup parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

inductive HasEffect : LanguageWriterTree sig α → EffectLanguage → Type where
  | ret : HasEffect (.ret value) (principal 1)
  | tell : HasEffect tree language →
      HasEffect (.tell message tree)
        (EffectLanguage.seq (principal [EffectAtom.base 0]) language)
  | free : (∀ response, HasEffect (continuation response) language) →
      HasEffect (.free interface operation lookup parameter continuation)
        (EffectLanguage.seq (principal [EffectAtom.free interface]) language)
  | subeffect : HasEffect tree lower → lower ≤ upper → HasEffect tree upper

def HasEffect.weaken (typing : HasEffect tree lower) (bound : lower ≤ upper) :
    HasEffect tree upper := .subeffect typing bound

noncomputable def HasEffect.bind
    (treeTyping : HasEffect tree language)
    (nextTyping : ∀ value, HasEffect (next value) nextLanguage) :
    HasEffect (tree.bind next) (EffectLanguage.seq language nextLanguage) := by
  induction treeTyping with
  | ret =>
      rw [EffectLanguage.seq_one_left]
      exact nextTyping _
  | tell tailTyping ih =>
      rw [EffectLanguage.seq_assoc]
      exact HasEffect.tell ih
  | free continuationTyping ih =>
      rw [EffectLanguage.seq_assoc]
      exact HasEffect.free ih
  | subeffect inner bound ih =>
      exact ih.weaken (EffectLanguage.seq_mono bound
        (EffectLanguage.le_refl nextLanguage))

inductive Observes : LanguageWriterTree sig α → List LanguageVal → α → Type where
  | ret : Observes (.ret value) [] value
  | tell : Observes tree log value →
      Observes (.tell message tree) (message :: log) value

/-- Structural relations used by graph and TT liftings. -/
inductive Rel (relation : α → β → Prop) :
    LanguageWriterTree sig α → LanguageWriterTree sig β → Prop where
  | ret : relation left right → Rel relation (.ret left) (.ret right)
  | tell : Rel relation left right →
      Rel relation (.tell message left) (.tell message right)
  | free : (∀ response, Rel relation (left response) (right response)) →
      Rel relation (.free interface operation lookup parameter left)
        (.free interface operation lookup parameter right)

theorem Rel.bind
    (treeRelation : Rel relation left right)
    (nextRelation : ∀ {a b}, relation a b →
      Rel resultRelation (leftNext a) (rightNext b)) :
    Rel resultRelation (left.bind leftNext) (right.bind rightNext) := by
  induction treeRelation with
  | ret related => exact nextRelation related
  | tell related ih => exact .tell ih
  | free related ih => exact .free ih

end LanguageWriterTree
end EffectSemantics
