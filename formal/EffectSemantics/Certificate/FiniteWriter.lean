import EffectSemantics.Denotational.LanguageGradedWriter
import EffectSemantics.Denotational.TypedWriterTT

namespace EffectSemantics

open TypedWriterTree

/-- Concrete algebra certificate extracted from proved declarations. -/
structure EffectLanguageCert where
  seqAssociative : ∀ first second third,
    EffectLanguage.seq (EffectLanguage.seq first second) third =
      EffectLanguage.seq first (EffectLanguage.seq second third)
  leftUnit : ∀ language,
    EffectLanguage.seq (EffectLanguage.principal 1) language = language
  rightUnit : ∀ language,
    EffectLanguage.seq language (EffectLanguage.principal 1) = language
  principalMultiplication : ∀ left right,
    EffectLanguage.seq (EffectLanguage.principal left)
      (EffectLanguage.principal right) =
      EffectLanguage.principal (left * right)
  handlerMonotone : ∀ {lower upper selected replacement}, lower ≤ upper →
    EffectLanguage.handle selected replacement lower ≤
      EffectLanguage.handle selected replacement upper

theorem effectLanguageCert : EffectLanguageCert where
  seqAssociative := EffectLanguage.seq_assoc
  leftUnit := EffectLanguage.seq_one_left
  rightUnit := EffectLanguage.seq_one_right
  principalMultiplication := EffectLanguage.principal_seq
  handlerMonotone := EffectLanguage.handle_mono

/-- Concrete monad/functor/graded-bind certificate for response-typed trees. -/
structure TypedWriterMonadCert (sig : Signature) where
  bindRightUnit : ∀ {α : Type} (tree : TypedWriterTree sig α),
    tree.bind TypedWriterTree.ret = tree
  bindAssociative : ∀ {α β γ : Type} (tree : TypedWriterTree sig α)
    (first : α → TypedWriterTree sig β)
    (second : β → TypedWriterTree sig γ),
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second)
  mapIdentity : ∀ {α : Type} (tree : TypedWriterTree sig α),
    tree.map id = tree
  mapComposition : ∀ {α β γ : Type} (first : α → β) (second : β → γ)
    (tree : TypedWriterTree sig α),
    (tree.map first).map second = tree.map (second ∘ first)
  languageBind : ∀ {α β : Type} {tree : TypedWriterTree sig α}
    {language nextLanguage : EffectLanguage}
    {next : α → TypedWriterTree sig β},
    HasLanguageEffect tree language →
    (∀ value, HasLanguageEffect (next value) nextLanguage) →
    HasLanguageEffect (tree.bind next)
      (EffectLanguage.seq language nextLanguage)

noncomputable def typedWriterMonadCert (sig : Signature) :
    TypedWriterMonadCert sig where
  bindRightUnit := TypedWriterTree.bind_ret
  bindAssociative := TypedWriterTree.bind_assoc
  mapIdentity := TypedWriterTree.map_id
  mapComposition := TypedWriterTree.map_comp
  languageBind := HasLanguageEffect.bind

structure TypedWriterAdequacyCert (sig : Signature) where
  operationalTree : ∀ {term resultTy effect}
      {typing : HasComp sig [] term resultTy effect}
      {log value},
    Nonempty (TypedWriterRuns sig typing log value) ↔
      Nonempty (Σ tree, ProducesTypedWriterTree sig typing tree ×
        TypedWriterTree.Observes tree log value)
  gradeSound : ∀ {term resultTy effect}
      {typing : HasComp sig [] term resultTy effect}
      {tree} (_produces : ProducesTypedWriterTree sig typing tree),
    TypedWriterTree.HasEffect tree effect

noncomputable def typedWriterAdequacyCert (sig : Signature) :
    TypedWriterAdequacyCert sig where
  operationalTree := typed_writer_operational_tree_adequacy
  gradeSound := ProducesTypedWriterTree.effectSound

structure TypedFiniteWriterCert (sig : Signature) where
  monad : TypedWriterMonadCert sig
  adequacy : TypedWriterAdequacyCert sig
  effects : EffectLanguageCert

noncomputable def typedFiniteWriterCert (sig : Signature) :
    TypedFiniteWriterCert sig where
  monad := typedWriterMonadCert sig
  adequacy := typedWriterAdequacyCert sig
  effects := effectLanguageCert

/-- Concrete finite shallow certificate.  Exhaustive clause grading is the
only supplied local premise; structural, graph, TT and exact-grade transport
are filled by checked generic proofs. -/
structure TypedFiniteShallowCert (sig : Signature) (selected : Nat)
    (handler : TypedWriterTree.AffineSemantics sig) (replacement : Effect) where
  exhaustiveEffect : TypedWriterTree.ExhaustiveEffect selected handler replacement
  mapNatural : ∀ {α β : Type} (function : α → β)
      (tree : TypedWriterTree sig α),
    (TypedWriterTree.shallow selected handler tree).map function =
      TypedWriterTree.shallow selected handler (tree.map function)
  relationPreserved : ∀ {α β : Type} {relation : α → β → Prop}
      {left : TypedWriterTree sig α} {right : TypedWriterTree sig β},
    TypedWriterTree.Rel relation left right →
    TypedWriterTree.Rel relation
      (TypedWriterTree.shallow selected handler left)
      (TypedWriterTree.shallow selected handler right)
  ttPreserved : ∀ {α β : Type} {relation : α → β → Prop}
      {left : TypedWriterTree sig α} {right : TypedWriterTree sig β},
    TypedWriterTree.Rel relation left right →
    TypedWriterTree.TT relation
      (TypedWriterTree.shallow selected handler left)
      (TypedWriterTree.shallow selected handler right)
  exactGrade : ∀ {α : Type} {tree : TypedWriterTree sig α} {effect : Effect},
    TypedWriterTree.ExactEffect tree effect →
    TypedWriterTree.HasEffect (TypedWriterTree.shallow selected handler tree)
      (TypedWriterTree.replaceFirst selected replacement effect)

noncomputable def typedFiniteShallowCert
    {sig : Signature} {selected : Nat}
    {handler : TypedWriterTree.AffineSemantics sig} {replacement : Effect}
    (exhaustive : TypedWriterTree.ExhaustiveEffect selected handler replacement) :
    TypedFiniteShallowCert sig selected handler replacement where
  exhaustiveEffect := exhaustive
  mapNatural := TypedWriterTree.shallow_map
  relationPreserved := fun related => related.shallow selected handler
  ttPreserved := fun related => related.shallowTT selected handler
  exactGrade := fun typing => typing.shallow exhaustive

end EffectSemantics
