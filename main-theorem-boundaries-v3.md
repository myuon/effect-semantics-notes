# Main theorem boundaries v3

## Status

**Counterclaim checklist for the main theorem.**  These boundaries are part of
the result, not deferred footnotes.

## 1. Unordered rows are may-information

The row

$$
\rho=\{\Delta,\Gamma\}
$$

means that either interface may be exposed.  It does not record:

- whether either occurs;
- occurrence count;
- operation order;
- which branch produces it;
- whether execution reaches it before divergence.

Deep discharge removes one possible outward label; it does not prove that a
matching clause executes.

## 2. Exact old base grades are not generic

Writer and State counterexamples show that identical old input grade, row, and
single-clause grade may produce different exact handled base effects.  Exception
shows that scope can matter even with one occurrence.

Therefore the main theorem preserves base operational/denotational behavior and
declared observations, but does not synthesize a principal transformed old
effect grade.

Such a theorem requires an additional `BaseEffectAbstraction` interaction
operator tracking count, order, scope, closure, or a coarse top.

## 3. Multi-shot is not universally valid

The syntax permits a resumption to be used zero or many times.  Writer, pure
State, and Exception supply ordinary duplicable computation functions, so their
models interpret this syntax.

A linear resource, region, one-shot continuation, or external IO base may not.
It must either:

- restrict handler typing to affine/linear use;
- provide explicit duplicability/discardability laws;
- change the handler capability profile.

The generic theorem cannot infer resource validity from monad laws.

## 4. Recursive observation levels differ

A bottom-only model identifies:

- silent divergence;
- infinitely many Writer actions before no boundary;
- infinitely many transient State updates before no boundary;
- infinitely many internally handled requests before no outward boundary.

This is adequate for Level 2 but not Level 3.  Productive infinite-trace
adequacy needs visible coinductive actions or guarded interaction trees.

## 5. Handler commutation is not preserved automatically

The main theorem preserves each handler's intended scope.  It does not assert
that different handlers commute.

In particular,

$$
\mathsf{Try}\circ H_\Delta
\neq
H_\Delta\circ\mathsf{Try}
$$

when a new operation clause raises an old exception.  Similar distinctions can
arise for State rollback, transactions, masking, resources, and concurrency.

## 6. Existence is structural, not automatic

Recursion-free semantics needs suitable initial resumption algebras.  Recursive
semantics needs recursive-domain/final-coalgebra/guarded solutions plus an
iteration theory.

Accessible polynomial-like Writer, State, and Exception instances satisfy the
chosen constructions.  Full powerset, unrestricted continuation, class-sized
signatures, or noncontinuous primitives may fail the package assumptions.

## 7. Adequacy is not full abstraction

Adequacy says operational observations and denotational observations agree.  It
does not say every denotational distinction is contextually observable.

Full abstraction would require a separate definability/context lemma and is not
part of the main theorem.

## 8. Count remains optional

Occurrence counts strengthen the handler output bound for affine resumptions,
but are unnecessary for unordered safety, discharge, conservativity, or
adequacy.  Under unrestricted recursion, a reachable recursive cycle normally
forces the corresponding finite count to $\infty$.

Thus count is a refinement of the main theorem, not one of its premises.

## 9. Honest summary

The positive result is broad but conditional:

> the extension preserves exactly the safety, iteration, observation, and
> relational certificates explicitly supplied by the base package.

The negative result is equally important:

> unordered row information and monad structure alone do not determine precise
> old-effect interaction, resource validity, handler commutation, or productive
> infinite behavior.
