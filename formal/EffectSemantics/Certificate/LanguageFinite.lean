import EffectSemantics.Denotational.LanguageSourceShallow
import EffectSemantics.Denotational.LanguageWriterTT

namespace EffectSemantics

open EffectLanguage

/-- The ordered effect-language algebra needed by the finite extension. -/
structure LanguageEffectCert where
  seqAssociative : ∀ first second third,
    seq (seq first second) third = seq first (seq second third)
  leftUnit : ∀ language, seq (principal 1) language = language
  rightUnit : ∀ language, seq language (principal 1) = language
  handlerMonotone : ∀ {lower upper selected replacement}, lower ≤ upper →
    handleWith selected replacement lower ≤ handleWith selected replacement upper
  handlerReturn : ∀ {selected replacement input}, principal 1 ≤ input →
    principal 1 ≤ handleWith selected replacement input
  handlerMatch : ∀ {selected replacement suffix input},
    seq (principal [EffectAtom.free selected]) suffix ≤ input →
    seq replacement suffix ≤ handleWith selected replacement input

theorem languageEffectCert : LanguageEffectCert where
  seqAssociative := seq_assoc
  leftUnit := seq_one_left
  rightUnit := seq_one_right
  handlerMonotone := fun bound =>
    handleWith_mono (EffectLanguage.le_refl _) bound
  handlerReturn := pure_le_handleWith
  handlerMatch := seq_replacement_le_handleWith

/-- The response-typed tree model, including its graded bind and finite
operational adequacy theorem. -/
structure LanguageWriterCert (sig : LanguageSignature) where
  bindRightUnit : ∀ {α : Type} (tree : LanguageWriterTree sig α),
    tree.bind LanguageWriterTree.ret = tree
  bindAssociative : ∀ {α β γ : Type} (tree : LanguageWriterTree sig α)
      (first : α → LanguageWriterTree sig β)
      (second : β → LanguageWriterTree sig γ),
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second)
  gradedBind : ∀ {α β : Type} {tree : LanguageWriterTree sig α}
      {first second : EffectLanguage} {next : α → LanguageWriterTree sig β},
    LanguageWriterTree.HasEffect tree first →
    (∀ value, LanguageWriterTree.HasEffect (next value) second) →
    LanguageWriterTree.HasEffect (tree.bind next) (seq first second)
  gradeSound : ∀ {term resultTy effect}
      {typing : HasLanguageComp sig [] term resultTy effect} {tree},
    ProducesLanguageWriterTree sig typing tree →
    LanguageWriterTree.HasEffect tree effect
  adequacy : ∀ {term resultTy effect}
      {typing : HasLanguageComp sig [] term resultTy effect} {log value},
    Nonempty (LanguageWriterRuns sig typing log value) ↔
      Nonempty (Σ tree, ProducesLanguageWriterTree sig typing tree ×
        LanguageWriterTree.Observes tree log value)

noncomputable def languageWriterCert (sig : LanguageSignature) :
    LanguageWriterCert sig where
  bindRightUnit := LanguageWriterTree.bind_ret
  bindAssociative := LanguageWriterTree.bind_assoc
  gradedBind := LanguageWriterTree.HasEffect.bind
  gradeSound := ProducesLanguageWriterTree.effectSound
  adequacy := language_writer_operational_tree_adequacy

/-- Properties of every semantic shallow handler; no handler-specific law is
assumed for naturality, relation lifting, or TT lifting. -/
structure LanguageShallowCert (sig : LanguageSignature) where
  mapNatural : ∀ {α β : Type} (selected : Nat)
      (handler : LanguageWriterTree.AffineSemantics sig)
      (function : α → β) (tree : LanguageWriterTree sig α),
    LanguageWriterTree.map function
        (LanguageWriterTree.shallow selected handler tree) =
      LanguageWriterTree.shallow selected handler
        (LanguageWriterTree.map function tree)
  relationPreserved : ∀ {α β : Type} {relation : α → β → Prop}
      {left : LanguageWriterTree sig α} {right : LanguageWriterTree sig β},
    LanguageWriterTree.Rel relation left right →
    ∀ selected handler,
      LanguageWriterTree.Rel relation
        (LanguageWriterTree.shallow selected handler left)
        (LanguageWriterTree.shallow selected handler right)
  ttPreserved : ∀ {α β : Type} {relation : α → β → Prop}
      {left : LanguageWriterTree sig α} {right : LanguageWriterTree sig β},
    LanguageWriterTree.Rel relation left right →
    ∀ selected handler,
      LanguageWriterTree.TT relation
        (LanguageWriterTree.shallow selected handler left)
        (LanguageWriterTree.shallow selected handler right)

theorem languageShallowCert (sig : LanguageSignature) :
    LanguageShallowCert sig where
  mapNatural := fun _selected _handler function tree =>
    LanguageWriterTree.shallow_map function tree
  relationPreserved := fun related selected handler =>
    related.shallow selected handler
  ttPreserved := fun related selected handler =>
    related.shallowTT selected handler

/-- Finite ordered-language structure preservation theorem.  For every base
signature, adjoining typed free requests and affine shallow handling yields a
well-typed source calculus, a graded response tree model, operational/tree
adequacy, and relation/TT-compatible shallow elimination.  Matching source
commutation is supplied by `ProducesLanguageWriterTree.answerWith`. -/
structure LanguageFiniteStructureCert (sig : LanguageSignature) where
  effects : LanguageEffectCert
  writer : LanguageWriterCert sig
  shallow : LanguageShallowCert sig
  preservation : ∀ {term next ctx resultTy effect},
    LanguageStep term next → HasLanguageComp sig ctx term resultTy effect →
      HasLanguageComp sig ctx next resultTy effect
  progress : ∀ {term resultTy effect},
    HasLanguageComp sig [] term resultTy effect → LanguageProgress term

noncomputable def languageFiniteStructurePreservation
    (sig : LanguageSignature) : LanguageFiniteStructureCert sig where
  effects := languageEffectCert
  writer := languageWriterCert sig
  shallow := languageShallowCert sig
  preservation := LanguageStep.preserve
  progress := HasLanguageComp.progressClosed

end EffectSemantics
