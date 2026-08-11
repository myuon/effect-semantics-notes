# Review guide and theorem dependency map

This is the canonical entry point for mathematical review.  The notes are
ordered **concrete programs first, abstract transport theorems second**.

## How formalization status is displayed

Every canonical chapter begins with a **Lean correspondence** panel.  We use
three labels.

| label | meaning |
|---|---|
| **Lean checked** | the displayed statement has a kernel-checked declaration; the link is authoritative |
| **Paper abstraction** | the note packages or generalizes checked component lemmas, but this exact formulation is not a Lean declaration |
| **Boundary / conjecture** | deliberately not claimed as proved; the missing condition or counterexample is part of the result |

Links of the form `lean/find/?pattern=...#doc` open the generated API search at
the exact declaration.  The complete cross-reference is also available in the
[Lean formalization index](lean-api-reference.md).
The remaining paper and partial obligations are tracked, without duplicate
entries, in the [formalization gap audit](formalization-gap-audit.md).

### Stable statement identifiers

Every definition, lemma, theorem, and corollary on the canonical proof path
has a globally unique identifier such as `C2-MAIN.6.1`.  The format is
`NOTE.SECTION.STATEMENT`: `C1`--`C4` name the concrete chapters, `MAIN` and
`PROOF` distinguish main-result and detailed-proof notes, and `LG`, `GF`, and
`GR` name the language-level, generic-finite, and generic-recursive theorem
notes.  These identifiers are stable: later insertions do not renumber an
existing statement.  Older labels such as “Theorem II.8” remain as readable
aliases.

## Canonical reading order

```{mermaid}
flowchart TD
  C1["Chapter I: run concrete base programs"] --> C1S["Fix base syntax, typing, and semantics"]
  C1S --> C2["Chapter II: add free operations and calculate examples"]
  C2 --> C2S["Extract the finite free-extension package"]
  C2S --> C3["Chapter III: calculate shallow handlers"]
  C3 --> C3S["Prove shallow naturality, relations, and adequacy"]
  C3S --> C4["Chapter IV: add fixpoint and derive deep handling"]
  C4 --> C4S["Prove finite/limit adequacy and recursive poles"]
  C4S --> A1["Abstract finite free-extension theorem"]
  A1 --> A2["Abstract recursive resumption theorem"]
  A2 --> A3["Functorial/package-level formulation and boundaries"]
```

The operational-example page comes first in every chapter.  Syntax and
denotation are introduced only after the intended behavior has been seen in
Writer, State, or Exception.

## Chapter I — fixed base language

Read in this order:

1. [Chapter overview and contract](chapter-1-overview-v5.md)
2. [Concrete base machines](chapter-1-operational-examples-v5.md)
3. [Core calculus and type safety](chapter-1-foundations-v5.md)
4. [Denotational models and operational comparison](chapter-1-denotational-v5.md)
5. [Exported base package](chapter-1-main-results-v5.md)
6. [Appendix I-A: detailed proofs](chapter-1-proof-details-v5.md)

### Definition and theorem correspondence

| note object | status | Lean declaration |
|---|---|---|
| values and computations | Lean checked | [`Val`, `Comp`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/Term.html) |
| ordered may-effect languages | Lean checked | [`EffectLanguage`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage#doc) |
| value/computation typing | Lean checked | [`HasLanguageVal`, `HasLanguageComp`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/LanguageCalculus.html) |
| CBV internal reduction | Lean checked | [`LanguageStep`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep#doc) |
| general computation application elaboration | Lean checked | [`HasLanguageComp.elaborateApplication`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.elaborateApplication#doc) |
| Evaluation-context presentation of CBV reduction | Lean checked; equivalent to finite `LanguageStep` | [`languageContextStep_iff_languageStep`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.languageContextStep_iff_languageStep#doc) |
| finite-to-recursive syntax and step embedding | Lean checked | [`LanguageComp.toRecursive`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageComp.toRecursive#doc), [`LanguageStep.toRecursive`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.toRecursive#doc) |
| preservation | Lean checked | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) |
| closed progress | Lean checked | [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc) |
| recursion-free internal normalization | Lean checked | [`HasLanguageComp.stronglyNormalizing`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.stronglyNormalizing#doc), [`HasLanguageComp.internallyNormalizesToBoundary`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.internallyNormalizesToBoundary#doc) |
| Writer/State/Exception model comparisons | Lean checked individually; typed graded signature bridge remains | [`genericWriterModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterModelComparison#doc), [`genericStateModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericStateModelComparison#doc), [`genericExceptionModelComparison`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericExceptionModelComparison#doc) |
| Writer operational/tree adequacy | Lean checked | [`language_writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_writer_operational_tree_adequacy#doc) |
| source-language preservation and tree semantics | Lean checked separately | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc), [`ProducesLanguageWriterTree`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree#doc) |
| categorical `BasePackage` presentation | Readable abstraction | exact instance boundary is stated in [package assumptions](chapter-1-main-results-v5.md) |

## Chapter II — free operations

The canonical semantic premise is now documented in
[Existence of the graded free monad transformer](graded-freet-existence-v1.md).
The grade-indexed carrier and root-exposure pages are alternative
implementation routes; `baseAct` is not a second independent main-theorem
premise because it is a field of `StrongGradedFreeT`, but constructing it is a
real object-side obligation.

Read the chapter as typed source → finite semantic core → conditional
graded theorem:

1. [Writer/State/Exception programs with free requests](chapter-2-operational-examples-v5.md)
2. [Added syntax and ordered effects](chapter-2-free-operations-v5.md)
3. [Writer end-to-end instance](writer-end-to-end-v5.md), [State](state-end-to-end-v5.md), [Exception](exception-end-to-end-v5.md)
4. [Finite denotation](chapter-2-denotational-v5.md)
5. [Free package](chapter-2-main-results-v5.md)
6. [Detailed proof appendix](chapter-2-proof-details-v5.md)

| note object | status | Lean declaration |
|---|---|---|
| exact return/internal/base/free progress | Lean checked | [`progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc) |
| current-language old-fragment conservativity | Lean checked | [`LanguageStep.preservesBaseOnly`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preservesBaseOnly#doc), [`baseOnly_boundary_is_base`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageSteps.baseOnly_boundary_is_base#doc) |
| typed operation signature | Lean checked | [`OperationSignature`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.OperationSignature#doc) |
| source Writer/free tree → generic free extension | Lean checked; bind preserving | [`LanguageWriterTree.toFreeExtension_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension_bind#doc) |
| finite base/free carrier | Lean checked | [`FreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc) |
| return and bind laws | Lean checked | [`FreeExtension.bind_ret`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.bind_ret#doc), [`FreeExtension.bind_assoc`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.bind_assoc#doc) |
| old-base embedding and erasure | Lean checked | [`embedBase`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.embedBase#doc), [`eraseFree_embedBase`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.eraseFree_embedBase#doc) |
| signature functoriality | Lean checked | [`mapSignature_id`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_id#doc), [`mapSignature_comp`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_comp#doc) |
| structural logical relation | Lean checked | [`FreeExtension.Rel`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel#doc) and [`Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc) |
| target-algebra fold | Lean checked | [`GenericExtensionAlgebra.fold_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.fold_bind#doc) |
| finite morphism lifting | Lean checked | [`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc) |
| finite relation lifting | Lean checked | [`GenericExtensionAlgebra.Relation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Relation.lift#doc) |
| finite TT lifting | Lean checked | [`GenericExtensionAlgebra.TTLayerAssumptions.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerAssumptions.lift#doc) |
| finite operational/denotational comparison transport | Lean checked | [`GenericExtensionAlgebra.ModelComparison.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc) |
| Chapter-II source metatheory | Lean checked as individual theorems | [`progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc) |

The ordered grade-indexed carrier in the chapter notes is a stronger paper
presentation. Lean now connects the source-specific finite tree to the generic
finite free extension, but does not identify either with the graded family
$F_eA$. The latter still requires the `StrongGradedFreeT` hypothesis.

## Chapter III — shallow handlers

1. [Concrete reductions](chapter-3-operational-examples-v5.md)
2. [Handler syntax and direct rules](chapter-3-shallow-handlers-v5.md)
3. [Denotational shallow handling](chapter-3-denotational-v5.md)
4. [Shallow package](chapter-3-main-results-v5.md)
5. [Detailed proof appendix](chapter-3-proof-details-v5.md)

| note object | status | Lean declaration |
|---|---|---|
| affine handler clauses | Lean checked | [`FreeExtension.AffineHandler`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.AffineHandler#doc) |
| forwarding shallow transformation | Lean checked | [`FreeExtension.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow#doc) |
| matching and forwarding equations | Lean checked | [`shallow_match`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_match#doc), [`shallow_forward`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_forward#doc) |
| map naturality | Lean checked | [`shallow_map`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_map#doc) |
| Chapter-III source progress and preservation | Lean checked separately | [`HasLanguageHandlerState.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageHandlerState.progressClosed#doc), [`LanguageShallowStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageShallowStep.preserve#doc) |
| structural relation preservation | Lean checked | [`Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.shallow#doc) |
| source-language shallow relation preservation | Lean checked | [`LanguageWriterTree.Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.Rel.shallow#doc) |
| matching source/tree commutation | Lean checked | [`ProducesLanguageWriterTree.answerWith`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc) |

## Chapter IV — recursion and derived deep handling

1. [Recursive programs](chapter-4-operational-examples-v5.md)
2. [Fixpoint and the derived handler](chapter-4-fixpoint-derived-deep-v5.md)
3. [Least-fixed-point denotation](chapter-4-denotational-v5.md)
4. [Recursive package](chapter-4-main-results-v5.md)
5. [Detailed proof appendix](chapter-4-proof-details-v5.md)

| note object | status | Lean declaration |
|---|---|---|
| finite-layer resumption system | Lean checked | [`RecursiveResumptionSystem`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem#doc) |
| derived-deep one-layer functional | Lean checked | [`RecursiveResumptionSystem.functional`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem.functional#doc) |
| fuel evaluator / finite iteration | Lean checked | [`genericRunFuel_eq_iterate`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel_eq_iterate#doc) |
| observer continuity obligations | Lean checked | [`RecursiveObserverContinuity`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveObserverContinuity#doc) |
| LFP unfold, leastness, adequacy, pole | Lean checked | [`GenericRecursiveResumption.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc) |
| recursive morphism lifting | Lean checked | [`GenericRecursiveMorphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveMorphism.lift#doc) |
| recursive relation lifting | Lean checked | [`GenericRecursiveRelation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveRelation.lift#doc) |
| recursive outcome-TT lifting | Lean checked | [`GenericRecursiveOutcomeTT.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveOutcomeTT.lift#doc) |
| old-language conservativity | Lean checked | [`oldLanguageConservative`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.oldLanguageConservative#doc) |
| Writer concrete fixed-point result | Lean checked | [`example_limit_true`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveWriter.example_limit_true#doc) |
| State limit adequacy | Lean checked | [`GenericRecursiveState.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveState.limit_adequacy#doc) |
| Exception limit adequacy | Lean checked | [`GenericRecursiveException.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveException.limit_adequacy#doc) |

## Abstract results — read only after Chapters I–IV

1. [Language-level structure-preservation theorem](language-graded-main-theorem-v6.md)
2. [Generic finite free-extension theorem](generic-free-extension-theorem-v1.md)
3. [Generic recursive resumption theorem](generic-recursive-resumption-theorem-v1.md)
4. [Functorial formulation](functorial-extension-theorem-v5.md)
5. [Categories of admissible packages](package-categories-v5.md)
6. [Assumption dependency audit](assumption-dependency-audit-v5.md)

The first three are the current formal core.  The functorial and categorical
pages are **Paper abstractions** of the checked Type-level construction unless
an individual statement links to a Lean declaration.

Only pages on the canonical proof path and explicitly retained research
context are published.  Superseded programs, intermediate explorations, and
archived theorem versions remain recoverable from Git history rather than
appearing alongside the current statements.
