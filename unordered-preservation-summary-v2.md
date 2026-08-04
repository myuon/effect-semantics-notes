# Unordered preservation summary v2

## Status

**Current main result for the version without counts or ordered traces.**

## Main theorem, layered statement

The unordered-row development supports three increasingly strong conclusions.

### Layer A: operational safety

Given `BaseSafety`, the extension preserves:

- deterministic decomposition;
- preservation of the new unordered row;
- effect-aware progress;
- empty-row unhandled-request safety;
- exhaustive deep discharge;
- old-language operational conservativity.

This layer does not require a base monad.

### Layer B: compositional denotation

Given a base monad $T$ and existing initial resumption solutions

$$
\mathsf{Res}_{T,\rho}A,
$$

the extension additionally preserves/provides:

- monadic sequencing;
- row-refined bind and weakening;
- canonical embedding of $T$;
- deep handlers as folds;
- base monad morphisms;
- compatible logical relations.

### Layer C: operational/denotational transfer

Given base soundness, observation reflection, semantic substitution, and
termination or an appropriate divergence model:

- operational steps preserve denotation;
- direct handlers commute with semantic folds;
- base adequacy lifts to the extended observations;
- related base observations lift through free operations and handlers.

## Assumption/result matrix

| Result | BaseSafety | base monad | resumption solution | base observation/reflection | termination/divergence model |
|---|---:|---:|---:|---:|---:|
| new-row preservation/progress | yes | no | no | no | no |
| deep discharge | yes | no | no | no | no |
| old operational conservativity | yes | no | no | no | no |
| row-refined denotation | no | yes | yes | no | no |
| base denotation embedding | no | yes | yes | no | no |
| morphism/relation lifting | no | yes | yes | relation-specific | no |
| one-step soundness | yes | yes | yes | base rule soundness | no |
| adequacy | yes | yes | yes | yes | yes or conditional |

## Precise meaning of elimination

For unordered may-rows,

$$
\rho\cup\{\Delta\}
\xrightarrow{H_\Delta}
\omega,
\qquad
\Delta\notin\omega
$$

means:

> no unhandled request belonging to interface $\Delta$ can escape the handled
> computation or its resumed continuations.

It does not mean:

- a $\Delta$ request occurs on every execution;
- the handler clause executes exactly once;
- the interpretation has no old base effects;
- the continuation is resumed exactly once;
- the old base effect grade is unchanged.

## Strongest unconditional conservativity claim

Adding syntax and semantics is conservative on old programs:

$$
\llbracket M\rrbracket_{\mathrm{new}}
=
\mathsf{lift}_T(\llbracket M\rrbracket_{\mathrm{old}})
$$

for every old term $M$.

Wrapping an old term in an arbitrary new handler is not itself an old-language
embedding and need not be observationally inert.  Identity or
observation-preserving return clauses give the qualified inertness theorem.

## Principal limitations

The unordered theorem deliberately forgets occurrence count and order.  The
Writer and State impossibility results prove that no exact old-grade transformer
can be reconstructed from:

$$
(\text{input old grade},\text{unordered row},\text{one clause grade})
$$

alone.

Exception additionally shows that old/new handler scope affects base outcomes
even when occurrence count is one.

Therefore a proposed theorem claiming exact preservation of arbitrary old
effect grades must add at least one of:

- restrictions on clauses/resumptions;
- algebraic laws collapsing repeated/reordered behavior;
- quantitative occurrence information;
- ordered/scope-sensitive refinement;
- a deliberately coarse top or closure.

## Current answer to the research question

For the unordered version, the answer is:

> User-defined first-order operations and exhaustive deep handlers can be added
> conservatively to a broad operational and monadic base while preserving the
> new effect-safety discipline, compositional resumption semantics, morphisms,
> logical relations, and—under the usual observation hypotheses—adequacy.
> What is not automatic is a precise transformation of the pre-existing base
> effect abstraction.

This is the baseline against which the optional count refinement should be
measured.  The count version should strengthen only the occurrence-sensitive
conclusions, not replace this theorem.
