# Chapter III — shallow-handler proofs and `ShallowCert`

## Status

**Conditional paper theorem.**  The affine fragment has a derived effect
transformer.  The general fragment is conditional on a supplied handler-effect
certificate.

## 1. Typing preservation

### Lemma III.1 — continuation typing

If

$$
\mathcal E[\mathsf{op}_{\Delta,i}(V)]:A!e_{\mathsf{in}},
$$

then residual-context typing gives an effect $e_k$ such that

$$
k=\lambda r.\mathcal E[\mathsf{return}\,r]
:
R_i\xrightarrow{e_k}A.
$$

The ordered input bound contains the primitive grade $\Delta$ before $e_k$,
up to the declared weakening.

### Theorem III.2 — handler preservation

Assume every clause type-checks at the output selected by $\Phi_h$ and its
local certificate covers return, match and forwarding.  If

$$
\Gamma\vdash M:A!e,
$$

then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:C!\Phi_h(e),
$$

and every handler reduction preserves this type and bound.

### Proof

`SH-Ret` uses value substitution.  `SH-Match` uses parameter substitution and
Lemma III.1 for $k$.  `SH-Forward` uses the free-request typing rule and the
structural handler-typing induction for its rewrapped continuation.  Reductions
inside the scrutinee use Chapter-II preservation. $\square$

## 2. Affine effect theorem

### Theorem III.3

Let the scrutinee have bound $b\cdot\Delta\cdot e$, where $b$ is
$\Delta$-free.  Let every response clause
have bound $e'$, invoke the continuation exactly once, and assume $1\leq e'$.
Then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:A!(b\cdot e'\cdot e).
$$

### Proof

On a matching request, residual-context typing identifies the bare tail at
$e$; response sequencing gives $e'\cdot e$, and the already evaluated prefix
contributes $b$.  If the optional request is absent, the computation follows a
path bounded by $b\cdot e$, and

$$
b\cdot e\leq b\cdot e'\cdot e
$$

follows from $1\leq e'$ and monotonicity.  The return rule is identity. $\square$

This theorem is an upper-bound theorem, not an assertion that every run reaches
$\Delta$.

## 3. Operational/denotational commutation

### Theorem III.4

For every closed recursion-free handled computation,

$$
\llbracket
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
\rrbracket
=
\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket).
$$

### Proof sketch

Induct on the finite outer base/free structure supplied by `FreeCert`.

- return uses the return equation;
- an internal/base step uses functoriality and Chapter-II soundness;
- a matching request uses semantic substitution for $p$ and $k$;
- a nonmatching request rebuilds the same constructor and uses the induction
  hypothesis pointwise on its rewrapped continuation.

The matching case deliberately does not apply the induction hypothesis to its
bare continuation.  This distinguishes shallow from deep handling.

## 4. Adequacy preservation

### Theorem III.5

Assume `FreeCert`, constructor-separated observations, and clauses related to
their denotations.  Then ground adequacy is preserved by the shallow handler:
operational returns, base outcomes, matching replacements and forwarded
requests agree with the structural shallow denotation.

### Proof

Combine Theorem III.4 with Chapter-II finite adequacy.  Clause computations use
the fundamental relation for ordinary source terms; captured continuations use
the pointwise continuation clause from `FreeCert`. $\square$

## 5. Conservativity

Adding the handler syntax does not alter reduction or denotation of terms that
do not use it.  Moreover, the affine identity handler is observationally the
identity on computations whose bound contains no matching $\Delta$, subject to
transparent forwarding.

The latter statement does not say that a general handler with a nontrivial
return clause is identity on old programs.

## 6. Chapter-III structure-preservation theorem

### Theorem III.6 — Shallow certificate

From `FreeCert` and either

1. exhaustive affine response clauses with $1\leq e'$, or
2. a general handler equipped with a valid monotone $\Phi_h$ certificate,

we obtain

$$
\mathsf{ShallowCert}(\Delta,h,\Phi_h)
$$

containing:

- handler typing preservation and effect-aware progress;
- the direct return/match/forward equations;
- the affine transformation
  $b\cdot\Delta\cdot e\mapsto b\cdot e'\cdot e$;
- operational/denotational commutation;
- ground adequacy preservation;
- old-language conservativity;
- explicit non-morphism and transparent-forwarding boundaries.

## 7. What is passed to Chapter IV

The residual-context, rule-analysis and finite-tree inductions are expanded in
[Chapter III — detailed shallow-handler proofs](chapter-3-proof-details-v5.md).

Chapter IV receives the standard shallow continuation interface, not just the
response-only sugar.  Nonmatching continuations already retain the shallow
handler; it recursively wraps matching continuations to derive deep handling.
It must add a recursion principle and
prove the resulting recursive effect bound; neither follows from
`ShallowCert` alone.
