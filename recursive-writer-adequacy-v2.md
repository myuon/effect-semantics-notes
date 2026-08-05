# Recursive Writer adequacy v2

## Status

**First finite-boundary and divergence adequacy decomposition for the recursive
Writer instance.**  Its former PCF-adequacy premise is discharged at paper level
by [Recursive Writer logical relation](recursive-writer-logical-relation-v2.md),
[fundamental lemma](recursive-writer-fundamental-v2.md), and [adequacy
closure](recursive-writer-adequacy-closure-v2.md).

## 1. Operational observations

For a closed configuration $\langle w,M\rangle$, define:

$$
\langle w,M\rangle\Downarrow\mathsf{ret}(u,a)
$$

when deterministic reduction reaches return with total log $u$, and

$$
\langle w,M\rangle\Downarrow
\mathsf{req}(u;\delta,i,p,K)
$$

when it reaches the first unhandled free request with accumulated log $u$.

Write

$$
\langle w,M\rangle\Uparrow_{\partial}
$$

when it takes infinitely many steps without reaching either boundary.  The
subscript emphasizes that this is boundary divergence, not a record of an
infinite action trace.

## 2. Finite approximants

Let $\llbracket M\rrbracket_n$ be the denotation obtained by allowing at most
$n$ recursive/handler unfoldings and replacing further unfolding by bottom.
Then

$$
\llbracket M\rrbracket_0
\sqsubseteq
\llbracket M\rrbracket_1
\sqsubseteq\cdots
$$

and

$$
\llbracket M\rrbracket
=\bigsqcup_n\llbracket M\rrbracket_n.
$$

Every finite return/request observation of the supremum already appears in some
finite approximant.  For an operation with an infinite response type, this
means the nominal root and every finite family of continuation observations;
the entire continuation function need not be compact.

## 3. One-step soundness

:::{prf:theorem} Recursive Writer one-step soundness
:label: thm-recursive-writer-step-soundness-v2

If

$$
\langle w,M\rangle\longrightarrow\langle w',M'\rangle,
$$

then

$$
\mathsf{prefix}_w(\llbracket M\rrbracket)
=
\mathsf{prefix}_{w'}(\llbracket M'\rrbracket).
$$
:::

:::{prf:proof}
The recursion-free cases are inherited from the finite Writer proof and extend
to directed suprema by continuity.  Recursive application uses the least-fixed-
point unfolding equation.  Handler matching and forwarding use the four
equations of {prf:ref}`thm-recursive-writer-handler-v2` plus semantic
substitution.
:::

## 4. Finite-boundary adequacy

:::{prf:theorem} Recursive Writer finite-boundary adequacy
:label: thm-recursive-writer-finite-adequacy-v2

For every closed first-order computation:

$$
\langle\epsilon,M\rangle
\Downarrow\mathsf{ret}(w,a)
\iff
\llbracket M\rrbracket=\mathsf{ret}_W(w,a),
$$

and

$$
\langle\epsilon,M\rangle
\Downarrow\mathsf{req}(w;\delta,i,p,K)
$$

iff the denotation has the corresponding root request with an operationally
related continuation.
:::

:::{prf:proof}
The forward directions iterate one-step soundness for the finite reduction.
For reflection, apply the recursive Writer fundamental lemma.  Its computation
relation turns the denotational root directly into a finite operational
boundary with the same constructor and Writer prefix.  Request continuations
are related pointwise through all finite projections; we do not assume that an
infinite-arity continuation is itself compact.
:::

Operational reflection is supplied by the fundamental logical-relations
theorem.  Domain continuity alone would prove soundness but not this direction.

## 5. Empty-row divergence adequacy

For $\rho=\varnothing$,

$$
\mathsf{CWTree}_\varnothing A\cong(W\times A)_\bot.
$$

:::{prf:theorem} Recursive Writer divergence adequacy
:label: thm-recursive-writer-divergence-adequacy-v2

For a closed ground computation with empty outward free row,

$$
\llbracket M\rrbracket=\bot
\iff
\langle\epsilon,M\rangle\Uparrow_{\partial}.
$$
:::

:::{prf:proof}
If execution terminated, finite-boundary soundness would give a nonbottom
return; an unhandled request is excluded by empty-row safety.  Conversely, if
the denotation were nonbottom, it would be a compactly witnessed Writer return,
and finite-boundary reflection would give termination.  Deterministic
decomposition leaves infinite reduction as the only remaining case.
:::

This theorem uses classical reasoning about deterministic execution and the
fundamental logical-relations theorem.  It does not distinguish silent
divergence from an infinite sequence of `tell` steps.

## 6. Handler adequacy

:::{prf:theorem} Recursive Writer handler correspondence
:label: thm-recursive-writer-handler-adequacy-v2

The operational deep handler and the least-fixed-point semantic handler agree
on every finite return/request observation.  At empty target row they also agree
on boundary divergence.
:::

:::{prf:proof}
Approximate both handlers by the number of permitted matching/unfolding steps.
The zero approximants are bottom.  The successor calculation is exactly the
operational return/matching/forwarding case split and the functional
$\Phi_h$.  Induction gives equality of finite approximants; continuity gives
the semantic supremum.  Apply finite-boundary and empty-row divergence adequacy.
:::

## 7. Examples

### Silent loop

```text
rec f(u). f(u)
```

Every finite approximation is bottom, so the supremum is bottom and the
program diverges.

### Finite handled request

```text
handle opDelta() with
  return x -> return x
  opDelta(_, k) -> tell("a"); k(())
```

The denotation is $\mathsf{ret}_W(a,())$, agreeing with one matching handler
step followed by return.

### Infinite handled requests

```text
handle (rec f(u). let _ <- opDelta() in f(u)) with
  return x -> return x
  opDelta(_, k) -> tell("a"); k(())
```

Every finite operational prefix writes another `a`, but no return/request
boundary is reached.  The partial Writer denotation is bottom.  This example
marks the exact boundary between divergence adequacy and infinite-trace
adequacy.

## 8. Established and remaining conclusions

At paper level the Writer calculation supports:

- recursive one-step soundness;
- finite return/request adequacy from the fundamental logical relation;
- empty-row boundary-divergence adequacy;
- recursive deep discharge;
- agreement with the finite semantics on recursion-free programs.

Still open before promoting the fully generic recursive theorem:

1. choose and construct the recursive-domain solution in a standard domain
   category;
2. formalize admissibility and continuity for the complete source language;
3. state the exact iteration-preserving morphism and admissible relation laws;
4. decide whether productive infinite traces belong in the main observation or
   remain optional.
