# Recursive deep adequacy reconstruction v4

## Status

**Proof architecture reconstructed from recursive algebraic-effect adequacy and
core Eff, parameterized by an existing base certificate.**

## 1. Why denotational equations are not enough

A complete-Elgot resumption supplies a mathematically coherent solution to
recursive equations.  A continuous deep-handler map supplies coherent handler
equations.  Neither fact alone proves that a source program and its denotation
have the same observable behavior.

Adequacy requires a relation connecting:

$$
\text{operational configurations}
\quad\text{and}\quad
\text{elements of }\mathsf{R}_{T,\rho}A.
$$

The relation must be admissible so that the recursion case can pass from finite
approximants to a least fixed point.

## 2. Boundary approximation relation

For each value type $A$, define a value relation
$d\mathrel{\triangleleft_A}V$.  For computations, define
$t\mathrel{\triangleleft_{A,\rho}}M$ by the following observations:

1. if $t=\bot$, it is related to every $M$;
2. if $t$ is a returned semantic value, $M$ reaches a corresponding returned
   source value;
3. if $t$ is a classified old base boundary, $M$ reaches the related old
   boundary supplied by the base certificate;
4. if $t$ is a free request node, $M$ reaches the same nominal request with
   related parameter and pointwise-related continuations.

The direction is intentionally approximation: bottom carries no positive
operational information.  Boundary reflection follows when the denotation is
non-bottom and has a separated outer constructor.

## 3. Admissibility

For every closed $M$, require

$$
\{t\mid t\mathrel{\triangleleft}M\}
$$

to contain bottom and be closed under suprema of increasing chains.  In a
minimal recursive-domain presentation, this follows from the minimal invariant
construction or finite projections.  In a guarded/coinductive presentation,
replace CPO admissibility with the corresponding guarded relation principle.

This is the exact hypothesis used in the recursive-function proof:

$$
\forall n.\;\Phi^n(\bot)\mathrel{\triangleleft}M
\quad\Longrightarrow\quad
\bigsqcup_n\Phi^n(\bot)\mathrel{\triangleleft}M.
$$

## 4. Fundamental lemma

:::{prf:lemma} Recursive deep fundamental lemma
:label: lem-recursive-deep-fundamental-v4

Related environments map every well-typed value and computation to related
denotations and substitutions.
:::

The ordinary cases use the base certificate and structural closure under
return and bind.  The new cases are:

- **operation:** request constructors preserve the relation pointwise;
- **recursive function:** every finite unfolding is related by the body
  induction hypothesis, and admissibility closes the approximation chain;
- **deep handler:** use admissible induction on the input denotation.  Return
  uses the return clause.  A matching request uses the related clause and the
  induction hypothesis for $\mathcal H_h\circ k$.  A nonmatching request uses
  request compatibility with the same handled continuation;
- **multi-shot clause:** each use of $k$ is justified by the function relation;
  validity for the old base semantics is an explicit handler-compatibility
  obligation.

## 5. Adequacy levels

The fundamental lemma yields only what the base observation relation reflects.

### Level 1: finite boundary adequacy

If a closed denotation has a finite return, old boundary or free request at its
root, operational evaluation reaches the corresponding boundary.

### Level 2: divergence adequacy

For a deterministic, empty-new-row computation in a base package that reflects
bottom,

$$
\llbracket M\rrbracket=\bot
\quad\Longleftrightarrow\quad
M\text{ has no finite terminal boundary}.
$$

The reverse implication needs more than the fundamental lemma: determinism,
continuity/finite approximation, and the base bottom-reflection certificate.

### Level 3: productive infinite traces

This requires a semantic object that retains productive infinite observations
and a corresponding coinductive adequacy relation.  It is not obtained from a
partial Writer, State or Exception model whose only infinite observation is
bottom.

## 6. Deep discharge in the relation

If the target row excludes $\Delta$ and every clause is typed at that row, the
semantic handler has no target constructor for an escaping $\Delta$ node.
The fundamental lemma then implies:

> no finite operational prefix of the handled computation exposes an unhandled
> $\Delta$ request.

For a recursive computation this is a safety property quantified over all
finite prefixes.  It does not require the computation to terminate.

## 7. Separation from exact old-effect preservation

Adequacy says that the selected old observation agrees operationally and
denotationally.  It does not say that an existing static old-effect grade can
be transformed exactly through an arbitrary handler.

To claim an exact Writer, State or Exception grade, add a
`HandlerInteraction` certificate containing the relevant distributive law,
resource discipline or clause invariant.  Without it, the generic theorem
retains only the old observation relation and a sound coarse grade supplied by
the base instance.
