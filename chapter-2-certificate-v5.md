# Chapter II — preservation proofs and `FreeCert`

## Status

**Conditional paper theorem.**  This page proves the recursion-free free
extension properties relative to the explicit `BaseCert` and initial-algebra
hypotheses.

## 1. Substitution and preservation

### Lemma II.1 — substitution

The Chapter-I value/computation substitution lemmas remain valid after adding
free operations.

### New case

If

$$
\Gamma,x:A\vdash V:P_i,
$$

then value substitution gives

$$
\Gamma\vdash V[W/x]:P_i,
$$

and `T-Free` yields

$$
\Gamma\vdash
\mathsf{op}_{\Delta,i}(V[W/x]):R_i!\Delta.
$$

No continuation substitution case is needed in source syntax.

### Theorem II.2 — internal preservation

If $M:A!e$ and $M\to M'$, then $M':A!e$.  All principal reductions are old
Chapter-I rules; the only new form is inert until captured by a future handler.
Context preservation follows from ordered multiplication.

## 2. Effect-aware progress

### Theorem II.3 — extended decomposition

A closed well-typed computation uniquely returns, reduces internally, exposes
a base request, or exposes a free request of the response type declared by its
interface.

### Proof

Induction on syntax, reusing Chapter-I canonical forms.  The new operation case
is immediate.  In a sequencing context, unique decomposition of the left term
determines exactly one enclosing case. $\square$

### Corollary II.4 — empty-free-effect safety

If the extended bound contains no free-interface factor and weakening cannot
remove free factors, evaluation cannot expose a free request.

This is a may-effect safety result.  The converse is false: a term typed using
$1\leq\Delta$ may terminate without exposing $\Delta$.

## 3. Old-language operational conservativity

### Theorem II.5

For an old Chapter-I term, the Chapter-II transition relation and observations
coincide with the Chapter-I ones.

### Proof

Old syntax contains no `op` form.  Every internal and base-machine rule is
literally reused, while the new free-request case is unreachable.  Induction on
the unique machine run gives equality of observations. $\square$

## 4. Free-extension algebra

### Theorem II.6

Under the initial-algebra hypotheses of the denotational chapter,
$\mathsf F_\Sigma(T)$ is a strong $\widehat E$-graded monad with coherent
weakening, canonical base embedding $j$, and free operation interpretations.

### Proof sketch

Initiality defines bind as the unique algebra morphism extending a return
substitution.  The left unit, right unit and associativity equations are proved
by showing both sides are algebra morphisms with the same action on returns,
base structure and free generators.  Uniqueness makes them equal.  Strength
and weakening are lifted by the same recursion and inherit coherence from
$T$. $\square$

## 5. Denotational conservativity

### Theorem II.7

For every old typed term,

$$
\llbracket M\rrbracket_{\mathsf F}
=j\circ\llbracket M\rrbracket_T.
$$

### Proof

Induction on typing.  Return uses preservation of $\eta$ by $j$; `let` uses
preservation of graded bind; primitive operations use the definition of the
base lift; branching uses naturality; subeffecting uses weakening coherence.
$\square$

## 6. Operational/denotational correspondence

Extend the base observation domain with

$$
\mathsf{freeReq}_{\Delta,i}(p,k).
$$

The observation records a free request extensionally through its typed
response continuation.  For first-order ground examples this may be tested by
supplying every possible finite response and comparing the resulting base
observations.

### Theorem II.8 — finite adequacy lifting

Assume the Chapter-I ground adequacy certificate and separation of return,
base-terminal and free-request constructors.  Then for every closed
recursion-free Chapter-II computation:

1. a return is reflected by the return branch of its denotation;
2. a terminal base outcome is reflected by the outer base semantics;
3. an exposed free request is reflected by the corresponding free node;
4. related responses lead to related continuation observations.

### Proof sketch

Induct on the finite operational/denotational operation tree.  Base segments use
the Chapter-I certificate; the free case uses constructor separation and the
induction hypothesis pointwise on responses.  Termination ensures that no
coinductive argument is required. $\square$

## 7. Lifting morphisms and relations

If a base graded monad morphism

$$
q:T\Rightarrow U
$$

preserves primitive interpretations, strength and weakening, initiality gives
a unique lifted morphism

$$
\mathsf F_\Sigma(q):
\mathsf F_\Sigma(T)\Rightarrow\mathsf F_\Sigma(U)
$$

acting by $q$ on base layers and identically on free generators.

Likewise, a bind-compatible base logical relation lifts structurally through
returns, base layers and free nodes.  The free-node clause relates equal
operation tags, related parameters and pointwise-related continuations.

## 8. Chapter-II structure-preservation theorem

### Theorem II.9 — Free extension certificate

Let $P$ provide `BaseCert`, a first-order polynomial free signature, and the
required finite initial algebras.  Then the free-operation extension provides

$$
\mathsf{FreeCert}(\mathsf F_\Sigma(P))
$$

containing:

1. extended substitution, preservation and four-way decomposition;
2. ordered upper-bound effect safety;
3. old-language operational conservativity;
4. a strong graded free-extension monad;
5. the canonical base embedding and denotational conservativity;
6. lifting of compatible base morphisms and logical relations;
7. finite ground adequacy for returns, base outcomes and exposed requests.

### Boundary

The constructor inductions and initiality arguments are expanded in
[Chapter II — detailed free-extension proofs](chapter-2-proof-details-v5.md).

`FreeCert` does not yet define a handler, eliminate $\Delta$, support general
recursion, or prove that an effect bound is exact.  Those are genuinely later
chapters.  In particular, $1\leq\Delta$ intentionally permits a term annotated
with $\Delta$ to return without performing it.
