# Residual context typing v1

## Status

**Derived Stage 2 lemmas; exhaustive-interface restriction adopted.**

This page factors the preservation proof for the one-shot shallow matcher into
a typed evaluation-context lemma and separate matching/forwarding cases. The
factorization justifies the adopted restriction that a handler indexed by
$\Delta$ supplies a branch for every operation in $\Delta$.

## 1. Residual context judgment

For a sequencing evaluation context $\mathcal E$, write

$$
\Gamma\vdash
\mathcal E:R\xRightarrow{e}A
$$

to mean:

> if the hole supplies a returned value of type $R$, the residual computation
> produces an $A$ with effect at most $e$.

The rules are

$$
\frac{~}{
\Gamma\vdash[-]:A\xRightarrow{1}A
}
\tag{CT-Hole}
$$

and

$$
\frac{
\Gamma\vdash\mathcal E:R\xRightarrow{e}C
\qquad
\Gamma,x:C\vdash N:A!f
}{
\Gamma\vdash
\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N
:R\xRightarrow{ef}A
}.
\tag{CT-Let}
$$

The context judgment deliberately starts at a **returned value**, not at an
arbitrary computation. This makes its composition law exact.

## 2. Plugging lemma

### Lemma RC-001 — Returned-value plugging

If

$$
\Gamma\vdash\mathcal E:R\xRightarrow{e}A
$$

and

$$
\Gamma\vdash V:R,
$$

then

$$
\Gamma\vdash\mathcal E[\mathsf{return}\;V]:A!e.
$$

### Proof

Induction on the context derivation.

- `CT-Hole`: $\mathsf{return}\;V:R!1$ by `T-Return`.
- `CT-Let`: apply the induction hypothesis to the inner context and then
  `T-Let`, producing the product $ef$.

$\square$

### Lemma RC-002 — Computation plugging

More generally, if

$$
\Gamma\vdash Q:R!d
$$

under the same context derivation, then

$$
\Gamma\vdash\mathcal E[Q]:A!(de).
$$

### Proof

The same induction, with `T-Let` in both cases. $\square$

This is the precise residual-effect inversion needed by the matching rule.

## 3. Exposed free-request inversion

### Lemma RC-003 — Request/context factorization

Suppose

$$
M=\mathcal E[\operatorname{op}_\Gamma(V)]
$$

is well typed, where
$\operatorname{op}:P\to R\in\Gamma$. After removing final applications of
`T-Sub`, there exist a residual effect $e$ and a context derivation such that

$$
\vdash V:P,
\qquad
\vdash\mathcal E:R\xRightarrow{e}A,
$$

and the principal effect of $M$ is

$$
\Gamma\cdot e.
$$

Any larger displayed effect arises only by subeffecting.

### Proof

Induction on $\mathcal E$.

- At the hole, invert `T-Free-Op`; the effect is $\Gamma=\Gamma\cdot1$.
- At a `let`, invert `T-Let`, apply the induction hypothesis to its left
  premise, and append the effect of its body using `CT-Let`.
- Strip `T-Sub` before each inversion and compose its endpoint inequality at
  the end.

$\square$

This syntactic lemma describes the **remaining** computation. A base-machine
trace $b$ already produced before the exposed request is an additional dynamic
prefix, so the combined state is written

$$
b\mid\mathcal E[\operatorname{op}_\Gamma(V)].
$$

It should not be confused with claiming that the residual term itself still
has an unexecuted prefix $b$.

## 4. Matching preservation

Assume $H$ contains

$$
\operatorname{op}(x)\Rightarrow N,
\qquad
x:P\vdash N:R!e'.
$$

From RC-003 obtain

$$
\vdash\mathcal E:R\xRightarrow{e}A.
$$

Value substitution gives

$$
\vdash N[V/x]:R!e'.
$$

RC-001 gives, in context $r:R$,

$$
r:R\vdash\mathcal E[\mathsf{return}\;r]:A!e.
$$

Therefore `T-Let` derives

$$
\vdash
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;
\mathcal E[\mathsf{return}\;r]
:A!(e'e).
$$

With an already observed machine prefix $b$, the complete trace bound is

$$
be'e.
$$

This proves the effect order in `R-Handle-Match` without introducing a
continuation variable.

## 5. Forwarding preservation

If no clause matches, `R-Handle-Forward` emits the original request together
with the context $\mathcal E$. RC-003 gives its residual bound

$$
\Gamma e.
$$

Consequently the complete bound, including an observed base prefix $b$, remains

$$
b\Gamma e.
$$

The handler disappears, but the forwarded operation token $\Gamma$ does not.
This observation imposes a real constraint on handler typing.

## 6. Why the provisional elimination rule needs exhaustiveness

The provisional rule in [Shallow matcher calculus v1](shallow-matcher-calculus-v1.md)
assigned

$$
b\Delta e\longmapsto be'e.
$$

This is sound when every operation represented by the distinguished
$\Delta$ token is handled. It is not sound for a partial handler whose identity
fallback can forward an operation from that same interface.

For example, let $\Delta$ contain both

$$
\mathsf{choose}:1\to\mathsf{Bool}
\qquad\text{and}\qquad
\mathsf{fail}:1\to1.
$$

The handler

```text
handle_Delta M with { choose(_) -> return true }
```

handles a leading `choose`, but forwards a leading `fail`. The latter execution
still contains a $\Delta$ request. It therefore cannot in general be assigned an
output grade from which $\Delta$ has been removed.

The wildcard makes evaluation exhaustive as a case distinction; it does not
make operation elimination exhaustive.

## 7. Adopted core and deferred extension

### 7.1 Adopted exhaustive interface eliminator

If $H$ has a typed clause for every operation in $\Delta$, use

$$
\frac{
\Gamma\vdash M:A!(b\Delta e)
\quad
\forall(\operatorname{op}:P\to R\in\Delta).\;
\Gamma,x:P\vdash H_{\operatorname{op}}:R!e'
\quad
1\leq e'
}{
\Gamma\vdash\mathsf{handle}_\Delta M\;\mathsf{with}\;H
:A!(be'e)
}.
\tag{T-Handle-Exhaustive}
$$

Here every actual $\Delta$ request takes a matching branch, while a skipped
optional layer takes the identity path $be\leq be'e$.

### 7.2 Deferred partial one-shot matcher

A partial matcher is not included in the core language. If added later, it
would transform alternative traces differently:

$$
\begin{array}{rcl}
b\Delta_{\mathrm{matched}}e&\mapsto&be'e,\\
b\Gamma_{\mathrm{unmatched}}e&\mapsto&b\Gamma e,\\
be&\mapsto&be.
\end{array}
$$

A single plain word cannot necessarily express the least upper bound of these
three outputs. A sound general type system therefore needs at least one of:

1. sets/languages of ordered traces, with pointwise transformation;
2. effect rows with operation-level subtraction plus ordered residual effects;
3. joins in the grade algebra large enough to contain all three outputs;
4. an explicit effect transformer indexed by the handled clause set.

The operational idea remains coherent, but none of these presentations is
needed for the current main theorem.

A comparatively small future design is to refine interfaces: split $\Delta$
into a handled subinterface and a residual subinterface, then require the
handler to be exhaustive for the handled part. This avoids partiality only by
making operation-level distinctions visible in the effect index, so it is still
a genuine extension rather than notation for the current system.

## 8. Revised preservation statement

The correct first theorem is labelled rather than ordinary same-grade subject
reduction.

### Theorem RC-004 — One-shot local preservation

For a well-typed exposed handler state:

- a matching transition replaces the request result and changes residual bound
  $\Delta e$ to $e'e$;
- an unmatched forwarding transition preserves residual bound $\Gamma e$;
- a return transition preserves the completed value and adds no dynamic effect;
- none of these transitions reinstalls the handler.

### Proof

Matching is Section 4; forwarding is Section 5; return follows from
`T-Return`. Handler disappearance follows by inspection of the three operational
rules. $\square$

Ordinary preservation at one common output grade is then a corollary only after
choosing an effect algebra with suitable upper bounds, or after restricting to
`T-Handle-Exhaustive`.

## 9. Consequence for the denotational phase

The original map

$$
H_\Delta:\widehat T_{b\Delta e}A\to\widehat T_{be'e}A
$$

most directly describes the exhaustive interface eliminator. A partial matcher
with forwarding cannot have this codomain unless the denotation of
$\widehat T_{be'e}$ also contains the forwarded alternatives through an
upper-bound inclusion.

Hence the main denotational construction should first test:

1. the original $H_\Delta$ for exhaustive interfaces.

A trace-language transformer for partial one-shot matchers is deferred.

This separates a genuine mathematical issue from the already settled
operational notion of shallowness.
