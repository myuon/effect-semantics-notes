import EffectSemantics.Denotational.LanguageSourceShallow
import EffectSemantics.Denotational.LanguageWriterTT

namespace EffectSemantics

open EffectLanguage

/-- Kernel-checked core certificate for the fixed source calculus.  It keeps
the syntactic obligations separate from Writer-specific observation. -/
structure LanguageCoreCert (sig : LanguageSignature) where
  valueSubstitution : ∀ {source target} {value : FinLanguageVal} {ty}
      {subst : Nat → FinLanguageVal},
    source ⊢[sig] value :ᵥ ty →
    LanguageSubstPreserves sig source target subst →
    target ⊢[sig] value.subst subst :ᵥ ty
  computationSubstitution : ∀ {source target} {term : FinLanguageComp}
      {ty effect} {subst : Nat → FinLanguageVal},
    source ⊢[sig] term : ty ! effect →
    LanguageSubstPreserves sig source target subst →
    target ⊢[sig] term.subst subst : ty ! effect
  preservation : ∀ {term next : FinLanguageComp} {ctx resultTy effect},
    term ⟶ next → ctx ⊢[sig] term : resultTy ! effect →
      ctx ⊢[sig] next : resultTy ! effect
  progress : ∀ {term : FinLanguageComp} {resultTy effect},
    [] ⊢[sig] term : resultTy ! effect → LanguageProgress term
  progressClassUnique : ∀ {term : FinLanguageComp}
      (first second : LanguageProgress term), first.kind = second.kind
  reductUnique : ∀ {term left right : FinLanguageComp},
    term ⟶ left → term ⟶ right → left = right
  canonicalBool : ∀ {value : FinLanguageVal}, [] ⊢[sig] value :ᵥ .bool →
    ∃ boolean, value = .bool boolean
  canonicalArrow : ∀ {value : FinLanguageVal} {domain latent codomain},
    [] ⊢[sig] value :ᵥ .arr domain latent codomain →
    (∃ body, value = .lam domain latent body) ∨
      (∃ allowed body, value = .fixLam allowed domain latent body)
  canonicalSum : ∀ {value : FinLanguageVal} {leftTy rightTy},
    [] ⊢[sig] value :ᵥ .sum leftTy rightTy →
    (∃ left, value = .inl left rightTy) ∨
      (∃ right, value = .inr leftTy right)

def languageCoreCert (sig : LanguageSignature) : LanguageCoreCert sig where
  valueSubstitution := fun typing preserves => typing.subst_preserved preserves
  computationSubstitution := fun typing preserves => typing.subst_preserved preserves
  preservation := LanguageStep.preserve
  progress := HasLanguageComp.progressClosed
  progressClassUnique := LanguageProgress.kind_unique
  reductUnique := LanguageStep.deterministic
  canonicalBool := HasLanguageVal.closed_bool_canonical
  canonicalArrow := HasLanguageVal.closed_arr_canonical
  canonicalSum := HasLanguageVal.closed_sum_canonical

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
  anchoredAffine : ∀ {selected pre replacement suffix},
    Effect.FreeOf selected pre →
    principal (pre * replacement * suffix) ≤
      handleWith selected (principal replacement)
        (principal (pre * [EffectAtom.free selected] * suffix))

theorem languageEffectCert : LanguageEffectCert where
  seqAssociative := seq_assoc
  leftUnit := seq_one_left
  rightUnit := seq_one_right
  handlerMonotone := fun bound =>
    handleWith_mono (EffectLanguage.le_refl _) bound
  handlerReturn := pure_le_handleWith
  handlerMatch := seq_replacement_le_handleWith
  anchoredAffine := anchored_replacement_le_handleWith

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
      {typing : [] ⊢[sig] term : resultTy ! effect} {tree},
    ProducesLanguageWriterTree sig typing tree →
    LanguageWriterTree.HasEffect tree effect
  semanticSequencing : ∀ {bound boundTy boundEffect body resultTy bodyEffect}
      {boundTyping : [] ⊢[sig] bound : boundTy ! boundEffect}
      {bodyTyping : boundTy :: [] ⊢[sig] body : resultTy ! bodyEffect}
      {tree : LanguageWriterTree sig (LanguageClosedVal sig boundTy)}
      (_boundProduces : ProducesLanguageWriterTree sig boundTyping tree)
      (continuation : LanguageClosedVal sig boundTy →
        LanguageWriterTree sig (LanguageClosedVal sig resultTy))
      (_bodyProduces : ∀ value, ProducesLanguageWriterTree sig
        (bodyTyping.subst0_preserved value.typing) (continuation value)),
    ProducesLanguageWriterTree sig (.letE boundTyping bodyTyping)
      (tree.bind continuation)
  internalStepInvariant : ∀ {term next resultTy effect}
      {typing : [] ⊢[sig] term : resultTy ! effect},
    (step : term ⟶ next) →
    ∀ {tree : LanguageWriterTree sig (LanguageClosedVal sig resultTy)},
      ProducesLanguageWriterTree sig (step.preserve typing) tree →
      ProducesLanguageWriterTree sig typing tree
  adequacy : ∀ {term resultTy effect}
      {typing : [] ⊢[sig] term : resultTy ! effect} {log value},
    Nonempty (LanguageWriterRuns sig typing log value) ↔
      Nonempty (Σ tree, ProducesLanguageWriterTree sig typing tree ×
        LanguageWriterTree.Observes tree log value)

noncomputable def languageWriterCert (sig : LanguageSignature) :
    LanguageWriterCert sig where
  bindRightUnit := LanguageWriterTree.bind_ret
  bindAssociative := LanguageWriterTree.bind_assoc
  gradedBind := LanguageWriterTree.HasEffect.bind
  gradeSound := ProducesLanguageWriterTree.effectSound
  semanticSequencing := ProducesLanguageWriterTree.letE
  internalStepInvariant := fun {term next resultTy effect} {typing} step
      {tree} produces =>
    ProducesLanguageWriterTree.internalStepInvariant (sig := sig) (term := term)
      (next := next) (resultTy := resultTy) (effect := effect)
      (typing := typing) step (tree := tree) produces
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

/-- Exact source-language certificate exported by Chapter II, before a
handler is added.  This separates the free-operation stage from the shallow
handler stage in the mechanized dependency graph. -/
structure LanguageFreeStageCert (sig : LanguageSignature) where
  core : LanguageCoreCert sig
  effects : LanguageEffectCert
  writer : LanguageWriterCert sig
  preservation : ∀ {term next : FinLanguageComp} {ctx resultTy effect},
    term ⟶ next → ctx ⊢[sig] term : resultTy ! effect →
      ctx ⊢[sig] next : resultTy ! effect
  progress : ∀ {term : FinLanguageComp} {resultTy effect},
    [] ⊢[sig] term : resultTy ! effect → LanguageProgress term

noncomputable def languageFreeStagePreservation
    (sig : LanguageSignature) : LanguageFreeStageCert sig where
  core := languageCoreCert sig
  effects := languageEffectCert
  writer := languageWriterCert sig
  preservation := LanguageStep.preserve
  progress := HasLanguageComp.progressClosed

/-- Exact source-language certificate exported by Chapter III. -/
structure LanguageHandlerStageCert (sig : LanguageSignature) where
  free : LanguageFreeStageCert sig
  shallow : LanguageShallowCert sig
  handlerPreservation : ∀ {ctx interface handler replacement input resultTy state next},
    HasLanguageAffineHandler sig ctx interface handler replacement →
    LanguageShallowStep state next →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy state →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy next
  handlerProgress : ∀ {interface handler replacement input resultTy term},
    HasLanguageHandlerState sig [] interface handler replacement input resultTy
      (.shallow interface handler term) →
    LanguageShallowProgress (.shallow interface handler term)

noncomputable def languageHandlerStagePreservation
    (sig : LanguageSignature) : LanguageHandlerStageCert sig where
  free := languageFreeStagePreservation sig
  shallow := languageShallowCert sig
  handlerPreservation := fun handlerTyping step typing =>
    step.preserve handlerTyping typing
  handlerProgress := HasLanguageHandlerState.progressClosed

/-- Finite ordered-language structure preservation theorem.  For every base
signature, adjoining typed free requests and affine shallow handling yields a
well-typed source calculus, a graded response tree model, operational/tree
adequacy, and relation/TT-compatible shallow elimination.  Matching source
commutation is supplied by `ProducesLanguageWriterTree.answerWith`. -/
structure LanguageFiniteStructureCert (sig : LanguageSignature) where
  core : LanguageCoreCert sig
  effects : LanguageEffectCert
  writer : LanguageWriterCert sig
  shallow : LanguageShallowCert sig
  preservation : ∀ {term next : FinLanguageComp} {ctx resultTy effect},
    term ⟶ next → ctx ⊢[sig] term : resultTy ! effect →
      ctx ⊢[sig] next : resultTy ! effect
  progress : ∀ {term : FinLanguageComp} {resultTy effect},
    [] ⊢[sig] term : resultTy ! effect → LanguageProgress term
  handlerPreservation : ∀ {ctx interface handler replacement input resultTy state next},
    HasLanguageAffineHandler sig ctx interface handler replacement →
    LanguageShallowStep state next →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy state →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy next
  handlerProgress : ∀ {interface handler replacement input resultTy term},
    HasLanguageHandlerState sig [] interface handler replacement input resultTy
      (.shallow interface handler term) →
    LanguageShallowProgress (.shallow interface handler term)

noncomputable def languageFiniteStructurePreservation
    (sig : LanguageSignature) : LanguageFiniteStructureCert sig where
  core := (languageHandlerStagePreservation sig).free.core
  effects := (languageHandlerStagePreservation sig).free.effects
  writer := (languageHandlerStagePreservation sig).free.writer
  shallow := (languageHandlerStagePreservation sig).shallow
  preservation := (languageHandlerStagePreservation sig).free.preservation
  progress := (languageHandlerStagePreservation sig).free.progress
  handlerPreservation := (languageHandlerStagePreservation sig).handlerPreservation
  handlerProgress := (languageHandlerStagePreservation sig).handlerProgress

end EffectSemantics
