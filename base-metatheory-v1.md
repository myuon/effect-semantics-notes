# Base metatheory v1

## Status

**Paper proofs for the recursion-free Stage 0 calculus.**

This page checks [Base calculus v1](base-calculus-v1.md) against [Base denotational semantics v1](base-denotational-semantics-v1.md). Free operations, handlers, and recursion are not involved.

## 1. Preliminary conventions

Contexts are interpreted as products. For a value derivation

$$
\Gamma\vdash V:A,
$$

write

$$
v=\llbracket V\rrbracket:
\llbracket\Gamma\rrbracket\to\llbracket A\rrbracket.
$$

The context-substitution morphism is

$$
\langle\mathsf{id},v\rangle:
\llbracket\Gamma\rrbracket
\to
\llbracket\Gamma\rrbracket\times\llbracket A\rrbracket
=
\llbracket\Gamma,x:A\rrbracket.
$$

All syntactic substitution below is capture-avoiding.

## 2. Syntactic substitution

### Lemma B-001a — Value substitution into values

If

$$
\Gamma,x:A\vdash W:C
$$

and

$$
\Gamma\vdash V:A,
$$

then

$$
\Gamma\vdash W[V/x]:C.
$$

### Lemma B-001b — Value substitution into computations

If

$$
\Gamma,x:A\vdash M:C!b
$$

and

$$
\Gamma\vdash V:A,
$$

then

$$
\Gamma\vdash M[V/x]:C!b.
$$

### Proof

Simultaneous induction on the value and computation typing derivations.

The only binders are $\lambda y.M$, `let y`, and the two case-branch variables. Rename them fresh before applying the induction hypothesis.

The base-operation case is immediate:

$$
\frac{
\beta:P\to R
\qquad
\Gamma,x:A\vdash W:P}
{
\Gamma,x:A\vdash\beta(W):R!|\beta|}.
$$

By the value induction hypothesis,

$$
\Gamma\vdash W[V/x]:P,
$$

and hence

$$
\Gamma\vdash\beta(W[V/x]):R!|\beta|.
$$

`T-Sub` preserves the same endpoint effect because substitution does not alter the proof of $b\leq c$. All other cases follow directly from their induction hypotheses. $\square$

## 3. Semantic substitution

### Lemma B-005 — Semantic value substitution

For

$$
\Gamma,x:A\vdash W:C
$$

and $\Gamma\vdash V:A$,

$$
\llbracket W[V/x]\rrbracket
=
\llbracket W\rrbracket
\circ
\langle\mathsf{id},\llbracket V\rrbracket\rangle.
$$

### Lemma B-006 — Semantic computation substitution

For

$$
\Gamma,x:A\vdash M:C!b
$$

and $\Gamma\vdash V:A$,

$$
\llbracket M[V/x]\rrbracket
=
\llbracket M\rrbracket
\circ
\langle\mathsf{id},\llbracket V\rrbracket\rangle.
$$

### Proof idea

Again use simultaneous induction. The variable, product, coproduct, abstraction, and application cases are the standard substitution lemma for the internal language of a bicartesian closed category.

The computation cases use naturality of:

- $\eta$ for return;
- strength and $\mu$ for `let`;
- $\beta^T$ only through ordinary composition for base operations;
- $\tau$ for subeffecting.

For example,

$$
\llbracket\beta(W[V/x])\rrbracket
=
\beta^T\circ\llbracket W[V/x]\rrbracket
$$

$$
=
\beta^T\circ\llbracket W\rrbracket
\circ\langle\mathsf{id},\llbracket V\rrbracket\rangle
$$

$$
=
\llbracket\beta(W)\rrbracket
\circ\langle\mathsf{id},\llbracket V\rrbracket\rangle.
$$

The `let` case is the only substantial diagram: reindexing the environment before graded bind equals reindexing both premises and then binding. This is exactly naturality of tensorial strength, followed by naturality of $\mu$. $\square$

## 4. Type preservation

### Theorem B-002 — Internal preservation

If

$$
\Gamma\vdash M:A!b
$$

and

$$
M\longrightarrow M',
$$

then

$$
\Gamma\vdash M':A!b.
$$

### Principal cases

#### `R-Beta`

Suppose

$$
\Gamma,x:C\vdash N:A!b
$$

and $\Gamma\vdash V:C$. Then

$$
(\lambda x.N)V\longrightarrow N[V/x].
$$

By B-001b,

$$
\Gamma\vdash N[V/x]:A!b.
$$

#### `R-Let-Return`

From

$$
\Gamma\vdash\mathsf{return}\;V:C!1_B
$$

and

$$
\Gamma,x:C\vdash N:A!b,
$$

the source has effect $1_B\cdot b=b$. B-001b gives

$$
\Gamma\vdash N[V/x]:A!b.
$$

#### Boolean branches

`T-If` requires both branches at the same effect $b$. Therefore selecting either branch preserves both result type and effect.

#### Sum branches

For `R-Case-Inl` and `R-Case-Inr`, use B-001b in the selected branch. `T-Case` already assigns both branches the common effect $b$.

#### Context rule

The only nontrivial context is

$$
\mathsf{let}\;x\leftarrow[-]\;\mathsf{in}\;N.
$$

If the hole computation preserves type $C$ and effect $c$, `T-Let` preserves the enclosing type and effect $c\cdot d$. $\square$

If the final typing rule of the source is `T-Sub`, apply the induction argument to its premise and then reapply the same endpoint inequality. Thus preservation is independent of whether the displayed principal term was typed directly or subsequently widened.

### Important boundary

Base-machine response

$$
\mathcal E[\beta(V)]
\rightsquigarrow
\mathcal E[\mathsf{return}\;W]
$$

is not an internal reduction and is not covered by B-002. It discharges an already observed effect. Its invariant must include the state/log of the selected base machine.

## 5. Canonical forms

For closed well-typed values:

- $V:1$ implies $V=*$;
- $V:\mathsf{Bool}$ implies $V=\mathsf{true}$ or $V=\mathsf{false}$;
- $V:A\times B$ implies $V=(V_1,V_2)$;
- $V:A+B$ implies $V=\mathsf{inl}\;W$ or $V=\mathsf{inr}\;W$;
- $V:A\to(B!b)$ implies $V=\lambda x.M$.

These follow by inspection of the closed value typing derivation. Primitive base values, if later added, require corresponding canonical-form clauses.

## 6. Unique request decomposition

Evaluation contexts are

$$
\mathcal E::=[-]
\mid
\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N.
$$

### Lemma B-007 — Unique request decomposition

If a closed computation contains a base request at the active call-by-value position and cannot take an internal step before it, then it has a unique presentation

$$
M=\mathcal E[\beta(V)].
$$

Uniqueness is syntactic because the context grammar follows only the left premise of nested `let`. Reduction never descends into an unchosen conditional/case branch or under a lambda.

## 7. Decomposition/progress

### Theorem B-003 — Deterministic decomposition

For every closed well-typed computation

$$
\vdash M:A!b,
$$

exactly one of the following holds:

1. $M=\mathsf{return}\;V$ for a closed value $V$;
2. $M=\mathcal E[\beta(V)]$ uniquely, exposing a base request;
3. there is a unique $M'$ such that $M\longrightarrow M'$.

### Proof

Induction on the syntax/typing of $M$.

- `return V` is case 1.
- $\beta(V)$ is case 2 with $\mathcal E=[-]$.
- For `let x <- M in N`, apply the induction hypothesis to $M$:
  - if $M=\mathsf{return}\;V$, use `R-Let-Return`;
  - if $M=\mathcal E[\beta(V)]$, the whole term is the unique extended request context;
  - if $M\to M'$, use `R-Context`.
- A closed application has a lambda in function position by canonical forms, so `R-Beta` applies.
- A closed conditional has `true` or `false`, selecting exactly one rule.
- A closed case scrutinee has exactly one injection form, selecting exactly one rule.

The three outcomes are disjoint by their outer syntax and unique-context decomposition. $\square$

## 8. Determinism

### Corollary B-008

If

$$
M\longrightarrow M_1
$$

and

$$
M\longrightarrow M_2,
$$

then

$$
M_1=M_2.
$$

This follows from B-003 and the non-overlap of principal rules.

## 9. Denotational soundness

### Theorem B-009 — Internal reduction soundness

For a fixed typing derivation at grade $b$, if

$$
\Gamma\vdash M:A!b
$$

and

$$
M\longrightarrow M',
$$

then

$$
\llbracket M\rrbracket
=
\llbracket M'\rrbracket:
\llbracket\Gamma\rrbracket
\to T_b\llbracket A\rrbracket.
$$

### Principal equations

#### `R-Beta`

Let

$$
n:\llbracket\Gamma\rrbracket\times\llbracket C\rrbracket
\to T_b\llbracket A\rrbracket
$$

interpret the body and let $v:\llbracket\Gamma\rrbracket\to\llbracket C\rrbracket$. Then

$$
\mathsf{ev}\circ\langle\Lambda(n),v\rangle
=
n\circ\langle\mathsf{id},v\rangle
$$

by the exponential $\beta$-law. By B-006, the right side is $\llbracket N[V/x]\rrbracket$.

#### `R-Let-Return`

Substitute $\eta\circ v$ for the first computation in the graded-bind composite. Coherence of strength with $\eta$, followed by the graded left-unit law

$$
\mu_{1_B,b}\circ\eta_{T_bA}=\mathsf{id}_{T_bA},
$$

reduces the composite to

$$
n\circ\langle\mathsf{id},v\rangle.
$$

By B-006 this is $\llbracket N[V/x]\rrbracket$.

#### Conditionals and cases

The coproduct $\beta$-laws

$$
[m,n]\circ\mathsf{inl}=m,
\qquad
[m,n]\circ\mathsf{inr}=n
$$

give the Boolean and sum reduction equations; B-006 handles substitution in case branches.

#### Context closure

The denotation of `let` is built functorially from composition, pairing, strength, $T_b(-)$, and $\mu$. Replacing the hole denotation by an equal morphism therefore preserves the enclosing denotation. $\square$

An outer `T-Sub` postcomposes both sides with the same $\tau_{b,c}$, so it also preserves the equality.

## 10. Subeffect coherence

The soundness statement above fixes compatible typing derivations. To make denotation depend only on the judgment rather than on the placement of `T-Sub`, require:

$$
\tau_{b,b}=\mathsf{id},
$$

$$
\tau_{c,d}\circ\tau_{b,c}=\tau_{b,d},
$$

and compatibility with graded bind:

$$
\tau_{b\cdot c,b'\cdot c'}\circ\mu_{b,c}
=
\mu_{b',c'}
\circ
T_{b'}(\tau_{c,c'})
\circ
\tau_{b,b',T_c(-)},
$$

for $b\leq b'$ and $c\leq c'$, with the necessary functor/coercion whiskering made explicit by the displayed types. Strength must commute with $\tau$ as well.

Under these axioms, adjacent subeffect coercions collapse to one, and coercions can be moved across `let`. A routine induction then gives derivation coherence for the current syntax.

This is an assumption on the semantic interface, not a consequence of having unrelated functors $T_b$.

## 11. What has and has not been established

Established at paper-proof level for Stage 0:

- syntactic substitution;
- internal preservation;
- canonical forms;
- unique request decomposition;
- progress modulo exposed base requests;
- determinism;
- internal reduction soundness, assuming the strong graded monad laws;
- sufficient coherence conditions for subeffecting.

Not yet established:

- adequacy for a particular base machine;
- a general operational/denotational logical relation;
- recursion soundness;
- any theorem about free operations or handlers.

The next small step can either prove Writer-machine adequacy for the concrete model, or begin Stage 1 as a conservative free-operation extension while retaining these Stage 0 lemmas as hypotheses.
