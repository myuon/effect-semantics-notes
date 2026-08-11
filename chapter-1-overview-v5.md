# Chapter I — concrete base languages

## Purpose

Chapter I establishes the **base case** used by every later extension.  It
does not yet add user-defined operations, handlers, or general recursion.
Instead, it fixes representative base machines, proves the common finite
language metatheory, relates execution to concrete monadic models, and exports
the package that Chapter II may assume.

The chapter follows one proof pipeline:

```text
concrete base machines
  → common typed CBV calculus
  → substitution / preservation / exact progress / determinism
  → operational and denotational graded models
  → model comparison
  → exported base package
```

Chapter I is therefore not the final extension theorem.  It supplies its
concrete base instances and isolates the assumptions that the extension
theorem must preserve.

## Fixed scope

Throughout this chapter:

- the source language is the finite mode `FinLanguageComp`;
- effects are upper bounds in the ordered base-effect algebra;
- internal evaluation is call-by-value small-step reduction;
- a base request is an operational boundary, not a stuck term;
- there are no free-operation nodes or handlers;
- recursion-free internal reduction is strongly normalizing in Lean;
- total execution across primitive boundaries additionally assumes a terminating
  response kernel;
- Writer is the most complete mechanized operational/denotational instance,
  while State and Exception supply additional concrete base models.

Chapter II adds free operations to this fixed base.  Chapter III adds shallow
handlers, and Chapter IV adds recursion and derives deep handling.

## Reading order

1. [Concrete base machines](chapter-1-operational-examples-v5.md) introduces
   evaluation contexts and shows what Writer, State, Exception, and Random
   requests do operationally.
2. [Core calculus and type safety](chapter-1-foundations-v5.md) fixes syntax,
   typing, effect annotations, and summarizes the common safety theorem.
3. [Denotational models and operational comparison](chapter-1-denotational-v5.md)
   interprets the same calculus in graded monads and states the required
   comparison with execution.
4. [Exported base package](chapter-1-main-results-v5.md) records the
   theorem statements and packages exactly what Chapter II may use.
5. [Appendix I-A: detailed proofs](chapter-1-proof-details-v5.md) contains the
   longer derivations and marks the remaining formalization boundaries.

The separate [model-architecture note](operational-denotational-comparison-v1.md)
gives a deeper explanation of why the operational monad $S$ and denotational
monad $T$ are kept distinct.  It is supporting architecture, not an additional
step in the Chapter I proof path.

## Chapter contract

At the end of Chapter I, later chapters may use the following results, with
the qualifications recorded in the package page:

| result | role | primary Lean correspondence |
|---|---|---|
| substitution | typing is stable under value replacement | [`HasLanguageComp.subst_preserved`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.subst_preserved#doc) |
| preservation | internal reduction preserves type and effect bound | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) |
| exact progress | exactly one of return, internal step, or boundary | [`progressClosed_exactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_exactlyOne#doc) |
| determinism | an internal reduct is unique | [`LanguageStep.deterministic`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.deterministic#doc) |
| semantic soundness | internal steps preserve the selected semantics | [`internalStepInvariant`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.internalStepInvariant#doc) |
| concrete adequacy | direct Writer execution agrees with its tree model | [`language_writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_writer_operational_tree_adequacy#doc) |
| finite structure package | checked finite source-language structure | [`LanguageFiniteTheory`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageFiniteTheory#doc) |

The readable paper-level name `BasePackage` additionally records the operational
model, denotational model, and their comparison.  It must not be read as a
claim that every concrete instance of that full record has already been
assembled in Lean.
