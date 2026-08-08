import EffectSemantics.Denotational.WriterTree

namespace EffectSemantics.WriterTree

/-- One-way ground observational lifting: every left Writer observation has a
right observation with the same log and related returned value. -/
def ObsRel (relation : α → β → Prop)
    (left : WriterTree α) (right : WriterTree β) : Prop :=
  ∀ {log leftValue}, Observes left log leftValue →
    ∃ rightValue, Observes right log rightValue ∧ relation leftValue rightValue

def Orthogonal (valueRelation : α → β → Prop)
    (resultRelation : γ → δ → Prop)
    (leftContext : α → WriterTree γ)
    (rightContext : β → WriterTree δ) : Prop :=
  ∀ {leftValue rightValue}, valueRelation leftValue rightValue →
    ObsRel resultRelation (leftContext leftValue) (rightContext rightValue)

/-- Biorthogonal/TT closure specialized to finite Writer observations. -/
def TT (valueRelation : α → β → Prop)
    (left : WriterTree α) (right : WriterTree β) : Prop :=
  ∀ {γ δ} (resultRelation : γ → δ → Prop)
    (leftContext : α → WriterTree γ) (rightContext : β → WriterTree δ),
    Orthogonal valueRelation resultRelation leftContext rightContext →
    ObsRel resultRelation (left.bind leftContext) (right.bind rightContext)

theorem Rel.toObsRel (treeRelation : Rel relation left right) :
    ObsRel relation left right := by
  intro log leftValue observed
  exact treeRelation.observes observed

/-- Structural lifting is contained in its observational TT closure. -/
theorem Rel.toTT (treeRelation : Rel relation left right) :
    TT relation left right := by
  intro γ δ resultRelation leftContext rightContext contexts
  induction treeRelation with
  | ret related => exact contexts related
  | tell related ih =>
      intro log leftValue observed
      cases observed with
      | tell tailObserved =>
          obtain ⟨rightValue, rightObserved, valueRelated⟩ := ih tailObserved
          exact ⟨rightValue, .tell rightObserved, valueRelated⟩
  | free related ih =>
      intro log leftValue observed
      cases observed

/-- The semantic shallow handler transports structural relations all the way
to the Writer TT closure. -/
theorem Rel.shallowTT (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics) :
    TT relation (WriterTree.shallow selected handler left)
      (WriterTree.shallow selected handler right) :=
  (treeRelation.shallow selected handler).toTT

/-- Observation reflection is exactly the identity-continuation instance of
TT. -/
theorem TT.reflectObservation
    {α β : Type} {relation : α → β → Prop}
    {left : WriterTree α} {right : WriterTree β}
    (tt : TT relation left right) : ObsRel relation left right := by
  let leftContext : α → WriterTree α := WriterTree.ret
  let rightContext : β → WriterTree β := WriterTree.ret
  have contexts : Orthogonal relation relation leftContext rightContext := by
    intro leftValue rightValue related
    intro log observedValue observed
    cases observed
    exact ⟨rightValue, .ret, related⟩
  intro log leftValue observed
  have boundObserved : Observes (left.bind leftContext) log leftValue := by
    simpa [leftContext, WriterTree.bind_ret] using observed
  obtain ⟨rightValue, rightObserved, related⟩ :=
    tt relation leftContext rightContext contexts boundObserved
  have finalObserved : Observes right log rightValue := by
    simpa [rightContext, WriterTree.bind_ret] using rightObserved
  exact ⟨rightValue, finalObserved, related⟩

end EffectSemantics.WriterTree
