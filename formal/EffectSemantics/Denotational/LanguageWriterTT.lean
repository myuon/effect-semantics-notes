import EffectSemantics.Denotational.LanguageTypedShallow

namespace EffectSemantics.LanguageWriterTree

def ObsRel (relation : α → β → Prop)
    (left : LanguageWriterTree sig α) (right : LanguageWriterTree sig β) : Prop :=
  ∀ {log leftValue}, Nonempty (Observes left log leftValue) →
    ∃ rightValue, Nonempty (Observes right log rightValue) ∧
      relation leftValue rightValue

def Orthogonal (valueRelation : α → β → Prop)
    (resultRelation : γ → δ → Prop)
    (leftContext : α → LanguageWriterTree sig γ)
    (rightContext : β → LanguageWriterTree sig δ) : Prop :=
  ∀ {leftValue rightValue}, valueRelation leftValue rightValue →
    ObsRel resultRelation (leftContext leftValue) (rightContext rightValue)

/-- TT closure of a value relation by all related Writer observation
contexts. -/
def TT (valueRelation : α → β → Prop)
    (left : LanguageWriterTree sig α) (right : LanguageWriterTree sig β) : Prop :=
  ∀ {γ δ} (resultRelation : γ → δ → Prop)
    (leftContext : α → LanguageWriterTree sig γ)
    (rightContext : β → LanguageWriterTree sig δ),
    Orthogonal valueRelation resultRelation leftContext rightContext →
    ObsRel resultRelation (left.bind leftContext) (right.bind rightContext)

theorem Rel.observes
    (treeRelation : Rel relation left right)
    (observed : Observes left log leftValue) :
    ∃ rightValue, Nonempty (Observes right log rightValue) ∧
      relation leftValue rightValue := by
  induction treeRelation generalizing log leftValue with
  | ret related =>
      cases observed
      exact ⟨_, ⟨.ret⟩, related⟩
  | tell related ih =>
      cases observed with
      | tell tailObserved =>
          obtain ⟨rightValue, ⟨rightObserved⟩, valueRelated⟩ := ih tailObserved
          exact ⟨rightValue, ⟨.tell rightObserved⟩, valueRelated⟩
  | free related ih => cases observed

theorem Rel.toObsRel (treeRelation : Rel relation left right) :
    ObsRel relation left right := by
  rintro log leftValue ⟨observed⟩
  exact treeRelation.observes observed

theorem Rel.toTT (treeRelation : Rel relation left right) :
    TT relation left right := by
  intro γ δ resultRelation leftContext rightContext contexts
  induction treeRelation with
  | ret related => exact contexts related
  | tell related ih =>
      rintro log leftValue ⟨observed⟩
      cases observed with
      | tell tailObserved =>
          obtain ⟨rightValue, ⟨rightObserved⟩, valueRelated⟩ := ih ⟨tailObserved⟩
          exact ⟨rightValue, ⟨.tell rightObserved⟩, valueRelated⟩
  | free related ih =>
      rintro log leftValue ⟨observed⟩
      cases observed

theorem Rel.shallowTT
    {sig : LanguageSignature} {α β : Type} {relation : α → β → Prop}
    {left : LanguageWriterTree sig α} {right : LanguageWriterTree sig β}
    (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics sig) :
    TT relation (LanguageWriterTree.shallow selected handler left)
      (LanguageWriterTree.shallow selected handler right) :=
  (treeRelation.shallow selected handler).toTT

theorem TT.reflectObservation
    {sig : LanguageSignature} {α β : Type} {relation : α → β → Prop}
    {left : LanguageWriterTree sig α} {right : LanguageWriterTree sig β}
    (tt : TT relation left right) : ObsRel relation left right := by
  let leftContext : α → LanguageWriterTree sig α := ret
  let rightContext : β → LanguageWriterTree sig β := ret
  have contexts : Orthogonal relation relation leftContext rightContext := by
    intro leftValue rightValue related
    rintro log observedValue ⟨observed⟩
    cases observed
    exact ⟨rightValue, ⟨.ret⟩, related⟩
  rintro log leftValue ⟨observed⟩
  have boundObserved : Observes (left.bind leftContext) log leftValue := by
    simpa [leftContext, bind_ret] using observed
  obtain ⟨rightValue, ⟨rightObserved⟩, related⟩ :=
    tt relation leftContext rightContext contexts ⟨boundObserved⟩
  have finalObserved : Observes right log rightValue := by
    simpa [rightContext, bind_ret] using rightObserved
  exact ⟨rightValue, ⟨finalObserved⟩, related⟩

end EffectSemantics.LanguageWriterTree
