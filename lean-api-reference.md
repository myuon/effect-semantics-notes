# Lean formalization index

This page connects the mathematical statements in the active research notes
to the exact declarations checked by Lean.  The complete generated library is
available in the [Lean API reference](https://myuon.github.io/effect-semantics-notes/lean/).

The links below point to declarations, not merely to source files.  A result
without such a link elsewhere in the notes should not be read as mechanized
solely because a related result appears here.

## Finite language and shallow handlers

| Mathematical result | Checked Lean declaration |
|---|---|
| Ordered effect-language laws and monotone handling | [`languageEffectCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageEffectCert#doc) |
| Preservation of internal CBV reduction | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) |
| Closed typed progress | [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc) |
| Reducibility and finite-language strong normalization | [`HasLanguageComp.reducible`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.reducible#doc), [`HasLanguageComp.stronglyNormalizing`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.stronglyNormalizing#doc) |
| Finite internal reduction to return or operation boundary | [`HasLanguageComp.internallyNormalizesToBoundary`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.internallyNormalizesToBoundary#doc) |
| General computation-application elaboration and typing | [`LanguageComp.elaborateApplication`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageComp.elaborateApplication#doc), [`HasLanguageComp.elaborateApplication`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.elaborateApplication#doc) |
| Writer finite base-model extraction | [`writerFiniteBaseModelCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.writerFiniteBaseModelCert#doc) |
| State finite base-model extraction | [`stateFiniteBaseModelCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.stateFiniteBaseModelCert#doc) |
| Exception finite base-model extraction | [`exceptionFiniteBaseModelCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.exceptionFiniteBaseModelCert#doc) |
| Writer operational/tree adequacy | [`language_writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_writer_operational_tree_adequacy#doc) |
| Shallow map naturality, structural-relation lifting and TT preservation | [`languageShallowCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageShallowCert#doc) |
| Bundled finite structure-preservation theorem | [`languageFiniteStructurePreservation`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageFiniteStructurePreservation#doc) |

## Generic finite free extension

| Mathematical result | Checked Lean declaration |
|---|---|
| Monad, base retraction, bind preservation and abstract shallow laws | [`genericFreeExtensionStructurePreservation`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeExtensionStructurePreservation#doc) |
| Identity law for signature mappings | [`FreeExtension.mapSignature_id`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_id#doc) |
| Composition law for signature mappings | [`FreeExtension.mapSignature_comp`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_comp#doc) |
| Structural logical relations are closed under bind | [`FreeExtension.Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc) |
| Algebra folds preserve bind | [`GenericExtensionAlgebra.fold_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.fold_bind#doc) |
| Monad morphisms lift through the free extension | [`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc) |
| Logical relations lift through the free extension | [`GenericExtensionAlgebra.Relation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Relation.lift#doc) |
| Observation-indexed TT-lifting contains structural tree relations | [`GenericExtensionAlgebra.TTLayerCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerCert.lift#doc) |
| Denotational-to-operational comparison lifts through finite free extension | [`GenericExtensionAlgebra.ModelComparisonCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparisonCert.lift#doc) |
| Legacy observation-oriented compatibility API | [`GenericExtensionAlgebra.AdequacyCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.AdequacyCert.lift#doc) |
| Existing Writer tree is recovered by round-trip | [`writerToGeneric_genericToWriter`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.writerToGeneric_genericToWriter#doc) |
| Generic Writer operational interpretation agrees with existing `runClosed` | [`genericWriterOperationalInterpretation_writerToGeneric`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterOperationalInterpretation_writerToGeneric#doc) |

## Recursive completion and derived deep handling

### Generic resumption construction

| Mathematical result | Checked Lean declaration |
|---|---|
| Observer-local conditions imply functional continuity | [`RecursiveObserverContinuity.functionalContinuous`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveObserverContinuity.functionalContinuous#doc) |
| Fuel evaluator agrees with finite Kleene iteration | [`genericRunFuel_eq_iterate`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel_eq_iterate#doc) |
| Unfold, leastness, adequacy and recursive pole | [`GenericRecursiveResumptionCert.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.main#doc) |
| Outcome morphism lifting | [`GenericRecursiveMorphismCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveMorphismCert.lift#doc) |
| Admissible relation lifting | [`GenericRecursiveRelationCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveRelationCert.lift#doc) |
| Observation-sensitive outcome TT lifting | [`GenericRecursiveOutcomeTTCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveOutcomeTTCert.lift#doc) |
| Recursive old-language conservativity | [`GenericRecursiveResumptionCert.oldLanguageConservative`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.oldLanguageConservative#doc) |
| Writer concrete limit result and pole | [`GenericRecursiveWriter.example_limit_true`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveWriter.example_limit_true#doc) |
| Exception limit adequacy | [`GenericRecursiveException.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveException.limit_adequacy#doc) |
| State transformer example | [`GenericRecursiveState.toggle_from_false`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveState.toggle_from_false#doc) |
| State recursive limit adequacy | [`GenericRecursiveState.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveState.limit_adequacy#doc) |

### Existing source-language instance

| Mathematical result | Checked Lean declaration |
|---|---|
| Continuity of the one-layer deep-Writer functional | [`languageDeepWriterFunctional_continuous`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageDeepWriterFunctional_continuous#doc) |
| Least-fixed-point unfold equation | [`languageDeepWriterSemantics_unfold`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageDeepWriterSemantics_unfold#doc) |
| Least pre-fixed-point property | [`languageDeepWriterSemantics_le_prefixed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageDeepWriterSemantics_le_prefixed#doc) |
| Operational/denotational adequacy of derived deep handling | [`language_deep_writer_semantic_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc) |
| Preservation of the result type at finite observations | [`languageDeepWriterSemantics_result_typed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageDeepWriterSemantics_result_typed#doc) |
| Writer instance of the recursive theorem | [`languageRecursiveStructurePreservation`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageRecursiveStructurePreservation#doc) |

## Base-independent transport

| Mathematical result | Checked Lean declaration |
|---|---|
| Abstract recursive structure preservation from local base obligations | [`LanguageRecursiveBaseCert.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveBaseCert.main#doc) |
| Outcome-morphism lifting through recursive completion | [`LanguageRecursiveMorphismCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveMorphismCert.lift#doc) |
| Logical-relation lifting through recursive completion | [`LanguageRecursiveRelationCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveRelationCert.lift#doc) |

## Ordered-subeffecting repair

| Mathematical result | Checked Lean declaration |
|---|---|
| First-occurrence replacement is not monotone on upper words | [`TypedWriterTree.replaceFirst_not_monotone`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedWriterTree.replaceFirst_not_monotone#doc) |
| Language-level handler transformation is monotone | [`EffectLanguage.handleWith_mono`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.handleWith_mono#doc) |
| Principal languages preserve sequential composition | [`EffectLanguage.principal_seq`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.principal_seq#doc) |
| A finite envelope bounds replacement under weakening | [`TypedWriterTree.replaceFirst_le_envelope`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedWriterTree.replaceFirst_le_envelope#doc) |

## How to read a declaration

Each declaration page shows the fully elaborated type checked by Lean and a
link back to its source.  The mathematical note explains why the hypotheses
are chosen and what the result means; the API page is the authoritative check
of the exact formal statement.
