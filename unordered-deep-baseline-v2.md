# Unordered/deep baseline v2

## Status

**Baseline specification, not a novelty claim.**

This page fixes the known reference point against which general base extensions will be measured.

## Language fragment

Start with recursion-free fine-grain CBV STLC.  Computations have judgments

$$
\Gamma\vdash M:A!\rho,
$$

where $\rho$ is a finite set or row of free-effect interfaces.

For the first pass, use finite sets:

$$
\rho,\sigma\in\mathcal P_{\mathrm{fin}}(\mathcal D),
\qquad
\rho\leq\sigma\iff\rho\subseteq\sigma.
$$

Sequencing and branching both use union at the effect level:

$$
\rho\otimes\sigma=\rho\cup\sigma,
\qquad
\rho\sqcup\sigma=\rho\cup\sigma.
$$

This intentionally forgets order, count, and whether an effect occurs on every branch.

## Operations

For an interface $\Delta$ containing $\operatorname{op}:P\to R$:

$$
\frac{\Gamma\vdash V:P}
{\Gamma\vdash\operatorname{op}_{\Delta}(V):R!\{\Delta\}}.
$$

An ordinary subsumption rule permits any larger row.

## Conditional join

$$
\frac{
\Gamma\vdash V:\mathsf{Bool}
\quad
\Gamma\vdash M:A!\rho
\quad
\Gamma\vdash N:A!\sigma
}{
\Gamma\vdash\mathbf{if}\ V\ \mathbf{then}\ M\ \mathbf{else}\ N
:A!(\rho\cup\sigma)
}.
$$

Thus

```text
if b then opΔ() else return ()
```

has effect $\{\Delta\}$, not a type-level sum of an operation tree and return.

## Deep handler behavior

An exhaustive handler for $\Delta$ has a return clause and one clause for every operation in $\Delta$.

The crucial operational points are:

1. A matching $\Delta$ request transfers control to its clause.
2. The captured continuation, when resumed, is placed under the same handler again.
3. A nonmatching $\Gamma$ request is forwarded, but its continuation retains the pending $\Delta$ handler.
4. Effects performed by the handler clause itself are outside the handled computation unless the syntax explicitly nests another handler.

Schematically, for matching $\Delta$:

$$
\operatorname{handle}_{\Delta}
  E[\operatorname{op}_{\Delta}(v)]
\operatorname{with}h
\longrightarrow
M_{\operatorname{op}}
\left[
v/x,
(\lambda y.\operatorname{handle}_{\Delta}E[\operatorname{return}y]\operatorname{with}h)/r
\right].
$$

For nonmatching $\Gamma$ the request is forwarded with continuation

$$
\lambda y.\operatorname{handle}_{\Delta}E[\operatorname{return}y]\operatorname{with}h.
$$

This differs from the previous first-actual-free-head shallow semantics, which ended the handler at a nonmatching free request.

## Static elimination

The intended typing shape is

$$
\frac{
\Gamma\vdash M:A!(\rho\cup\{\Delta\})
\qquad
\Gamma\vdash h:(A,\Delta)\Rightarrow_{\sigma}C
}{
\Gamma\vdash\operatorname{handle}_{\Delta}M\operatorname{with}h
:C!(\rho\cup\sigma)
}.
$$

Elimination means:

> any $\Delta$ request that would escape from the handled computation is interpreted here, so $\Delta$ is absent from the outward may-row unless a clause itself re-emits it.

It does not mean that every execution invokes a $\Delta$ clause.

## Tree semantics

For signature $\Sigma$:

$$
\mathsf{Tree}_{\Sigma}A
\cong
A+
\sum_{\operatorname{op}:P\to R\in\Sigma}
P\times(R\to\mathsf{Tree}_{\Sigma}A).
$$

The row-refined carrier is

$$
\mathsf{Tree}_{\rho}A
=
\{t\mid\text{every operation label in }t\text{ belongs to }\rho\}.
$$

A deep handler is a fold that recursively handles matching nodes and recursively preserves nonmatching nodes.  This makes the operational rules and denotational equations structurally parallel.

## Baseline property package

The baseline should establish, without claiming novelty:

- substitution and row weakening;
- preservation;
- effect-aware progress;
- no unhandled free operation for closed empty-row computations;
- deep elimination;
- operational/tree correspondence;
- conservativity over pure STLC;
- structural handler fusion laws where their clause algebras permit them.

Only after fixing this baseline do we replace the trivial base by a general [base semantic package](base-semantic-package-v2.md).

