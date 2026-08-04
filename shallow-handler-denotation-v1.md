# Shallow handler denotation v1

## Status

**First adopted Stage 3 construction: exhaustive handler over one optional free layer.**

This page constructs the denotation of the core shallow handler from the
optional-layer carrier. It is deliberately local: we assume the extended graded
monad and its weakening maps exist, then define $H_\Delta$ and verify its two
characteristic equations.

## 1. Assumed extended graded structure

Let $\widehat E$ be the ordered effect-word structure and

$$
\widehat T_E:\mathcal C\to\mathcal C
$$

an extended graded monad with:

$$
\widehat\eta_A:A\to\widehat T_1A,
$$

$$
\widehat\mu_{E,F}:
\widehat T_E\widehat T_FA
\to
\widehat T_{EF}A,
$$

and coherent weakening maps

$$
\widehat\tau_{E\leq F}:
\widehat T_EA\to\widehat T_FA.
$$

For a base grade $b\in B$ and free interface $\Delta$, assume the optional-layer
presentation

$$
\boxed{
\widehat T_{b\Delta e}A
\cong
T_b\left(
  \widehat T_eA
  +
  \mathsf{Op}_\Delta(\widehat T_eA)
\right)
}
$$

where

$$
\mathsf{Op}_\Delta Z
=
\coprod_{\operatorname{op}:P\to R\in\Delta}
P\times Z^R.
$$

The left summand is a skipped optional $\Delta$ boundary. The right summand is
one actual $\Delta$ request together with its result-indexed tail.

This carrier is the denotational counterpart of the direct operational
alternatives:

$$
\mathsf{return/tail}
\qquad\text{or}\qquad
\mathcal E[\operatorname{op}_\Delta(V)].
$$

## 2. Denotation of an exhaustive handler

Suppose every operation

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}
\in\Delta
$$

has a clause denotation

$$
c_{\operatorname{op}}:
P_{\operatorname{op}}
\to
\widehat T_{e'}R_{\operatorname{op}}.
$$

All clauses share the effect upper bound $e'$, and assume

$$
1\leq e'.
$$

We first define the local layer algebra

$$
h_{\Delta,e,e'}:
\widehat T_eA+
\mathsf{Op}_\Delta(\widehat T_eA)
\to
\widehat T_{e'e}A.
$$

### Skip branch

On the left summand,

$$
h_{\Delta,e,e'}(\mathsf{inl}(z))
=
\widehat\tau_{e=1e\leq e'e}(z).
\tag{H-Skip}
$$

This performs no clause effect. It only widens the no-operation path by the
static inequality $1\leq e'$.

### Operation branch

For

$$
(\operatorname{op},p,k)
\in
\mathsf{Op}_\Delta(\widehat T_eA),
$$

where

$$
k:R_{\operatorname{op}}\to\widehat T_eA,
$$

define

$$
h_{\Delta,e,e'}
(\mathsf{inr}(\operatorname{op},p,k))
=
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k.
\tag{H-Op}
$$

The right-hand side lies in

$$
\widehat T_{e'e}A.
$$

This is exactly the operational order “branch first, captured tail second.”

## 3. Lifting through the base prefix

Define

$$
\boxed{
H_\Delta^{b,e,e'}
=
T_b(h_{\Delta,e,e'})
:
\widehat T_{b\Delta e}A
\to
\widehat T_{be'e}A.
}
$$

Strictly, the codomain identification uses the recursive carrier equation for
$\widehat T_{be'e}A$. The conceptual operation is simply functorial mapping
through the outer base computation.

This explains why base operations before the first free request retain the
pending handler. The $T_b$ structure is executed/interpreted first, while
$h_{\Delta,e,e'}$ remains mapped over its result.

## 4. Characteristic equations

Let

$$
\mathsf{skip}_\Delta:
\widehat T_eA\to\widehat T_{\Delta e}A
$$

be the optional-layer insertion using $\mathsf{inl}$ and the outer unit. Then

$$
H_\Delta^{1,e,e'}
\circ
\mathsf{skip}_\Delta
=
\widehat\tau_{e\leq e'e}.
\tag{E-H-Value}
$$

This is the identity fallback equation. Runtime behavior is unchanged; only the
effect bound is widened.

For the canonical operation constructor

$$
\mathsf{op}_\Delta(p,k)
\in
\widehat T_{\Delta e}A,
$$

we have

$$
H_\Delta^{1,e,e'}
(\mathsf{op}_\Delta(p,k))
=
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k.
\tag{E-H-Op}
$$

These equations follow immediately by coproduct case analysis. Lifting through
$T_b$ gives the corresponding equations under a base prefix.

## 5. Why this denotation is shallow

A deep handler would recursively transform every tail $k(r)$:

$$
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
(\lambda r.H_\Delta(k(r))).
$$

Our definition instead uses

$$
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k.
$$

There is no recursive occurrence of $H_\Delta$. Therefore a later $\Delta$
operation in $k(r)$ is left exposed. Shallowness is visible directly in the
defining equation, independently of the operational presentation.

## 6. Why exhaustiveness matters

The operation summand is

$$
\coprod_{\operatorname{op}\in\Delta}
P_{\operatorname{op}}
\times
(\widehat T_eA)^{R_{\operatorname{op}}}.
$$

To define $h_{\Delta,e,e'}$ on this coproduct, one morphism is required for
every summand. These are precisely the exhaustive clauses
$c_{\operatorname{op}}$.

If a clause were absent, its summand would need to be forwarded into the
codomain. But $\widehat T_{e'e}A$ has removed the selected $\Delta$ layer and
provides no canonical place for that request. Partial matching therefore needs
a larger codomain retaining the unhandled summands, exactly as predicted by the
operational preservation analysis.

## 7. Concrete Writer calculation

Take the Writer base model and let the branch for

$$
\mathsf{choose}:1\to\mathsf{Bool}
$$

denote

$$
c_{\mathsf{choose}}(*)
=
([\text{"op"}],\mathsf{true}).
$$

Let the captured tail be

$$
k(x)=([\text{"tail"}],x).
$$

Then `H-Op` gives

$$
c_{\mathsf{choose}}(*)
\mathbin{\mathsf{bind}}
k
=
([\text{"op"},\text{"tail"}],\mathsf{true}).
$$

No recursive handler application occurs in $k$.

For a skipped layer containing

$$
z=([\text{"tail"}],\mathsf{false}),
$$

`H-Skip` returns the same Writer pair:

$$
h(\mathsf{inl}(z))
=
([\text{"tail"}],\mathsf{false}),
$$

viewed at the larger static grade $e'e$. Thus the branch log `"op"` is not
fabricated on the no-operation path.

## 8. Correspondence with the direct operational rules

| Direct operational outcome | Layer element | Denotational action |
|---|---|---|
| value/no $\Delta$ request | $\mathsf{inl}(z)$ | weaken $z$ without executing a clause |
| matching $\Delta$ request | $\mathsf{inr}(\operatorname{op},p,k)$ | run $c_{\operatorname{op}}(p)$, then bind into $k$ |
| base request in prefix | outer $T_b$ structure | map $h$ through $T_b$ |
| later request in tail | contained in $k(r)$ | unchanged; $h$ is not recursive |

An other-interface request at the selected head is not represented by the
$\Delta$ layer carrier. It belongs to a different effect-word summand or a more
general ambient-row presentation. The typed core rule applies only when the
selected layer is $\Delta$.

## 9. Naturality

For a value map $f:A\to A'$, polynomial functoriality and naturality of bind and
weakening give

$$
\widehat T_{be'e}(f)
\circ
H_{\Delta,A}^{b,e,e'}
=
H_{\Delta,A'}^{b,e,e'}
\circ
\widehat T_{b\Delta e}(f).
$$

The proof is case analysis on the optional layer:

- skip uses naturality of $\widehat\tau$;
- operation uses naturality of graded bind in its result.

Thus $H_\Delta$ is a natural transformation between the indicated grade
components.

## 10. What is proved and what remains

Given the assumed extended graded monad, optional-layer isomorphism, and
coherent weakening, we have constructed $H_\Delta$ and established:

1. correct typing $b\Delta e\to be'e$;
2. identity/skip equation;
3. operation-clause equation;
4. nonrecursive shallowness;
5. lifting through a base prefix;
6. naturality in the result type;
7. agreement with the concrete Writer examples.

The major remaining obligation is now sharply isolated:

> construct $\widehat T$ and its coherent optional-layer weakening from an
> arbitrary base graded monad $T$, rather than assuming them.

That construction must resolve the repeated-padding issue. The handler itself
does not introduce a further ambiguity once the optional layer is available.

There is also a more basic existence issue: inserting a layer in the middle of
$T_{be}$ generally requires a map $T_{be}\to T_bT_e$, opposite to graded
multiplication. This obstruction and the resulting construction choices are
analyzed in [Middle-padding obstruction v1](middle-padding-obstruction-v1.md).
