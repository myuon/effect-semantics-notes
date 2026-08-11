# Recursive TT-lifting and derived-deep audit

## Status

**Conditional reconstruction.**  The finite TT theorem does not automatically
survive fixpoints.  This page identifies the additional conditions and updates
the Chapter-IV proof boundary.

## 1. Why finite TT is insufficient

The recursion-free proof uses induction on finite operational/free trees.  A
recursive term instead denotes

$$
\operatorname{lfp}(F)=\bigsqcup_{n<\omega}F^n(\bot).
$$

To apply the fundamental lemma at the supremum, the computation relation must
be admissible.  Neither structural generation nor TT-closure alone guarantees
this in an arbitrary category.

## 2. Sufficient recursive TT conditions

For each grade $e$, require:

1. $S_eA$ and $T_eA$ are pointed $\omega$-cpos;
2. return, bind, weakening, base/free constructors and handlers are
   $\omega$-continuous;
3. every pole $\mathcal O_e$ contains related bottoms and is closed under
   pointwise suprema of related chains;
4. continuation spaces use the pointwise order;
5. the selected observation map is continuous at the declared observation
   level.

:::{prf:lemma} Admissibility of recursive TT
:label: lem-recursive-tt-admissible-v5

Under conditions (1)--(4), $V^{\top\top}_e$ is admissible whenever the value
relations used at recursive types are admissible.
:::

**Proof.**  The TT relation is an intersection, over all related continuation
pairs, of inverse images of the admissible pole under the continuous maps
$m\mapsto m\gg=k$ and $n\mapsto n\gg=\ell$.  Each inverse image contains
bottom and is closed under chain suprema; their intersection has the same
properties. $\square$

This proof requires the pole itself to be admissible.  Defining the pole by
exact finite termination observations generally fails that condition unless
bottom is included at an approximation level.

## 3. Observation levels

Three distinct recursive claims remain:

1. **Finite-boundary soundness.** Every observed finite return/request agrees
   with a compact semantic approximation.
2. **Termination/divergence adequacy.** Semantic bottom is equivalent to no
   finite terminal boundary.
3. **Productive infinite behavior.** Infinite visible interactions are
   compared coinductively.

`RecursiveAdequacyAssumptions` proves (1), and proves (2) only when
`RecursiveObservation` supplies bottom reflection. It does not prove (3) in a
partiality-only model.

## 4. Derived deep handler

Let $\mathcal D_h$ be the functional that performs one shallow pass and wraps
every matching resumption with its argument.  Under continuity,

$$
\mathsf{deep}^{\mathsf{derived}}_h
=\operatorname{lfp}(\mathcal D_h)
=\bigsqcup_n\mathcal D_h^n(\bot).
$$

At each finite approximant, the Chapter-III TT-compatible handler theorem
applies.  The admissibility lemma then relates the supremum.  This supplies the
previously implicit bridge from `TTClosure` to the recursive fundamental lemma.

## 5. Elimination and adequacy

Interface elimination is a finite-prefix safety property.  Every finite
reduction prefix uses finitely many unfoldings, so the finite approximant proof
shows that an exhaustive, outwardly $\Delta$-free derived handler exposes no
unhandled $\Delta$.

Adequacy is separate.  It follows only at the observation level for which the
recursive pole has a reflection theorem.  Thus elimination does not imply
termination, and bottom reflection does not imply productive-trace adequacy.

## 6. Concrete model consequences

- **Writer:** use the lifted recursive Writer/free-tree domain.  Finite log and
  request observations are compact; partiality gives Level 1 and, with the
  standard computational-adequacy argument, Level 2.
- **State:** use a pointwise state-to-partial-resumption domain.  Admissibility
  is checked at every initial state.
- **Exception:** use a separated bottom/return/error/request domain.
- **Random:** finite subdistributions are not by themselves closed under all
  increasing $\omega$-chains.  Recursive Random requires a dcpo of
  subprobability valuations/distributions and continuity of integration or
  finite-sum bind.  The recursion-free Random instance must not be imported
  unchanged.

## 7. Revised Chapter-IV theorem boundary

`RecursiveTTClosure` must explicitly supply an **admissible recursive pole** and
continuous TT operations, not merely an unspecified admissible relation.
`RecursiveModel` separately supplies the fixpoint model, and
`RecursiveObservation` supplies only the requested reflection level. Without
these records, `RecursiveSafety` still gives operational one-step safety;
interface elimination remains a separate finite-prefix theorem.
