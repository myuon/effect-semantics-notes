# Lean index: mathematical statements to declarations

This page connects the mathematical statements in the active research notes
to the exact declarations checked by Lean.  The complete generated library is
available in the [Lean API reference](https://myuon.github.io/effect-semantics-notes/lean/).

The links below point to declarations, not merely to source files.  A result
without such a link elsewhere in the notes should not be read as mechanized
solely because a related result appears here.

## Finite language and shallow handlers

| Mathematical result | Checked Lean declaration |
|---|---|
| Ordered effect-language associativity and monotone handling | [`EffectLanguage.seq_assoc`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.seq_assoc#doc), [`EffectLanguage.handleWith_mono`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.handleWith_mono#doc) |
| Preservation of internal CBV reduction | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) |
| Closed typed progress | [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc) |
| Reducibility and finite-language strong normalization | [`HasLanguageComp.reducible`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.reducible#doc), [`HasLanguageComp.stronglyNormalizing`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.stronglyNormalizing#doc) |
| Finite internal reduction to return or operation boundary | [`HasLanguageComp.internallyNormalizesToBoundary`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.internallyNormalizesToBoundary#doc) |
| General computation-application elaboration and typing | [`LanguageComp.elaborateApplication`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageComp.elaborateApplication#doc), [`HasLanguageComp.elaborateApplication`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.elaborateApplication#doc) |
| Writer finite base-model extraction | [`genericWriterModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterModelComparison#doc) |
| State finite base-model extraction | [`genericStateModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericStateModelComparison#doc) |
| Exception finite base-model extraction | [`genericExceptionModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericExceptionModelComparison#doc) |
| Writer operational/tree adequacy | [`language_writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_writer_operational_tree_adequacy#doc) |
| Shallow map naturality, structural-relation lifting and TT preservation | [`LanguageWriterTree.Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.Rel.shallow#doc) |
| Matching source/tree commutation | [`ProducesLanguageWriterTree.answerWith`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc) |

## Generic finite free extension

| Mathematical result | Checked Lean declaration |
|---|---|
| Monad structure of the generic free extension | [`genericFreeMonad`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeMonad#doc) |
| Base embedding preserves bind and has a retraction | [`FreeExtension.embedBase_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.embedBase_bind#doc), [`FreeExtension.eraseFree_embedBase`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.eraseFree_embedBase#doc) |
| Structural relation preserves bind and shallow handling | [`FreeExtension.Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc), [`FreeExtension.Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.shallow#doc) |
| Exact Chapter-II four-way progress | [`HasLanguageComp.progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc) |
| Base-only preservation and no free boundary | [`LanguageStep.preservesBaseOnly`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preservesBaseOnly#doc), [`FinLanguageSteps.baseOnly_boundary_is_base`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageSteps.baseOnly_boundary_is_base#doc) |
| Source Writer/free tree to generic free extension | [`LanguageWriterTree.toFreeExtension_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension_bind#doc) |
| Identity law for signature mappings | [`FreeExtension.mapSignature_id`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_id#doc) |
| Composition law for signature mappings | [`FreeExtension.mapSignature_comp`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_comp#doc) |
| Structural logical relations are closed under bind | [`FreeExtension.Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc) |
| Algebra folds preserve bind | [`GenericExtensionAlgebra.fold_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.fold_bind#doc) |
| Monad morphisms lift through the free extension | [`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc) |
| Logical relations lift through the free extension | [`GenericExtensionAlgebra.Relation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Relation.lift#doc) |
| Observation-indexed TT-lifting contains structural tree relations | [`GenericExtensionAlgebra.TTLayerAssumptions.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerAssumptions.lift#doc) |
| Denotational-to-operational comparison lifts through finite free extension | [`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc) |
| Existing Writer tree is recovered by round-trip | [`writerToGeneric_genericToWriter`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.writerToGeneric_genericToWriter#doc) |
| Generic Writer operational interpretation agrees with existing `runClosed` | [`genericWriterOperationalInterpretation_writerToGeneric`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterOperationalInterpretation_writerToGeneric#doc) |

## Recursive completion and derived deep handling

### Generic resumption construction

| Mathematical result | Checked Lean declaration |
|---|---|
| Observer-local conditions imply functional continuity | [`RecursiveObserverContinuity.functionalContinuous`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveObserverContinuity.functionalContinuous#doc) |
| Fuel evaluator agrees with finite Kleene iteration | [`genericRunFuel_eq_iterate`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel_eq_iterate#doc) |
| Unfold, leastness, adequacy and recursive pole | [`GenericRecursiveResumption.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc) |
| Outcome morphism lifting | [`GenericRecursiveMorphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveMorphism.lift#doc) |
| Admissible relation lifting | [`GenericRecursiveRelation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveRelation.lift#doc) |
| Observation-sensitive outcome TT lifting | [`GenericRecursiveOutcomeTT.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveOutcomeTT.lift#doc) |
| Recursive old-language conservativity | [`GenericRecursiveResumption.oldLanguageConservative`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.oldLanguageConservative#doc) |
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
| Writer instance of the recursive theorem | [`language_deep_writer_semantic_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc) |

## Base-independent transport

| Mathematical result | Checked Lean declaration |
|---|---|
| Abstract recursive structure preservation from local base obligations | [`LanguageRecursiveModel.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel.main#doc) |
| Outcome-morphism lifting through recursive completion | [`LanguageRecursiveMorphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveMorphism.lift#doc) |
| Logical-relation lifting through recursive completion | [`LanguageRecursiveRelation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveRelation.lift#doc) |

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
