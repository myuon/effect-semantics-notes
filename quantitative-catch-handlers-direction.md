# Quantitative catch handlers — future direction

## Status

**Separate research direction; definitions and theorem candidates only.**

This page does not change the adopted first-actual-free-head shallow handler.
It records a possible later calculus motivated by two goals:

1. statically track how many times an interface may occur on one execution path;
2. let a one-shot handler visibly discharge one occurrence of its handled
   effect.

## 1. Motivation

An unordered may-effect row records only

$$
\Delta\in E.
$$

It cannot distinguish one occurrence from several because

$$
\{\Delta\}\cup\{\Delta\}=\{\Delta\}.
$$

Consequently an ordinary shallow handler cannot generally remove $\Delta$ from
the row: after handling one occurrence, another may remain.

The proposed alternative records a pathwise occurrence upper bound

$$
\Delta^n,
\qquad
n\in\mathbb N_\infty
=
\{0,1,2,\ldots,\omega\}.
$$

$\Delta^1$ is an affine effect: every execution path performs $Delta$ at most
once.

## 2. Quantitative grade algebra

For multiple interfaces, a grade is a count vector

$$
\nu:\mathcal D\to\mathbb N_\infty.
$$

Interpret $\nu(\Delta)=n$ as “at most $n$ occurrences of $Delta$ on any one
execution path.” Define:

### Return

$$
\mathsf{return}:0.
$$

### Sequencing

$$
(\nu+\mu)(\Delta)
=
\nu(\Delta)+\mu(\Delta).
$$

### Branching

$$
(\nu\sqcup\mu)(\Delta)
=
\max(\nu(\Delta),\mu(\Delta)).
$$

### Subeffecting

$$
\nu\leq\mu
\quad\Longleftrightarrow\quad
\forall\Delta.\;\nu(\Delta)\leq\mu(\Delta).
$$

Thus a conditional with zero occurrences on one branch and one occurrence on
the other receives upper bound $1$ without requiring an exact-count union
$\{0,1\}$.

## 3. Why the current handler cannot always decrement

The adopted handler stops when it encounters another free interface. Hence

```text
Gamma; Delta
```

and

```text
Delta; Gamma
```

have the same unordered count vector, but $H_\Delta$ handles $Delta$ only in
the second program. A count-only rule

$$
n\longmapsto(n-1)^+
$$

would therefore be unsound for the current forwarding policy.

This is not a defect of counting. It says that occurrence information alone
does not imply **reachability by the handler**.

## 4. Catch-once operational policy

Introduce a distinct handler $C_\Delta$, which ignores other effects while
searching for the first matching $\Delta$. Once it handles one matching node,
it disappears.

On interaction trees:

$$
C_\Delta(\mathsf{ret}(x))
=
\mathsf{ret}(x),
$$

$$
C_\Delta(\mathsf{base}_\beta(p,k))
=
\mathsf{base}_\beta
(p,\lambda r.C_\Delta(k(r))),
$$

$$
C_\Delta
(\mathsf{free}_{\Gamma,\operatorname{op}}(p,k))
=
\mathsf{free}_{\Gamma,\operatorname{op}}
(p,\lambda r.C_\Delta(k(r)))
\quad(\Gamma\neq\Delta),
$$

$$
C_\Delta
(\mathsf{free}_{\Delta,\operatorname{op}}(p,k))
=
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k.
$$

The other-interface equation recursively retains the pending catch. The
matching equation contains no recursive call, so only one matching occurrence
is processed.

This can be described as:

> deep search, shallow resumption.

It differs intentionally from the main calculus, where another free interface
ends the handler.

## 5. Candidate quantitative typing rule

Suppose the input has $Delta$-count bound $n$, and the selected clause has
$\Delta$-count bound $k$. If captured continuations are resumed exactly once,
the candidate output is

$$
\boxed{
n\longmapsto(n-1)^++k,
}

where

$$
(n-1)^+=\max(n-1,0).
$$

If clauses are $Delta$-free,

$$
n\longmapsto(n-1)^+.
$$

In particular,

$$
\boxed{
\Delta^1\longmapsto\Delta^0.
}
$$

This is the desired affine elimination theorem: a catch-once handler discharges
an effect known to occur at most once per path.

## 6. Conditional effects

Conditional occurrence is compatible with upper counts. For

```text
if b then op_Delta(*) else return *
```

the input bound is $Delta^1$. On the true path the operation is caught; on the
false path there is nothing to catch. Both output paths have count zero, so

$$
C_\Delta(\mathsf{if}\;b\;\mathsf{then}\;\Delta\;\mathsf{else}\;\mathsf{return})
:\Delta^0.
$$

The difficulty returns only if $n$ is intended as an exact count. Exact
conditional information would require intervals $[\ell,u]$ or sets of possible
counts. The first version should use upper bounds.

## 7. Exactly-once continuation discipline

The decrement theorem relies on affine resumption.

If an intervening $Gamma$ request is handled by an outer construct that
duplicates its captured continuation, the pending $C_\Delta$ scope is also
duplicated and may catch one $Delta$ in each copy. Therefore the calculus must
provide at least one of:

- exactly-once implicit resumption, as in the current core;
- affine/linear continuation typing;
- a usage grade that multiplies effect counts under duplication;
- a path semantics in which nondeterministic alternatives are not sequentially
  accumulated.

The intended first version retains the current exactly-once implicit
continuation discipline.

## 8. Handler fuel

Generalize catch-once to a handler with fuel

$$
C_\Delta^m,
\qquad m\in\mathbb N_\infty.
$$

At a matching node, one unit of fuel is consumed:

$$
C_\Delta^{m+1}
(\mathsf{free}_\Delta(p,k))
=
c(p)\mathbin{\mathsf{bind}}
(\lambda r.C_\Delta^m(k(r))).
$$

Other effects preserve the same fuel while searching. For $Delta$-free
clauses, the expected count transformation is

$$
\boxed{
n\longmapsto(n-m)^+.
}

This produces a hierarchy:

| Fuel | Intended behavior |
|---:|---|
| $0$ | identity |
| $1$ | catch-once |
| finite $m$ | catch at most $m$ occurrences |
| $\omega$ | handle every reachable occurrence |

$m=\omega$ is a candidate bridge to deep handlers because
$\omega-1=\omega$.

## 9. Clause-scope choice for the deep limit

To compare $C_\Delta^\omega$ with standard deep handlers, fix whether the
handler is reinstalled around:

1. the captured continuation only;
2. both the clause body and captured continuation.

The proposed fuel equation handles only the resumed continuation. Clause-body
$\Delta$ effects remain outside the handler and contribute their own count
$k$. Rehandling clause effects could recursively generate new work and needs a
different transformer.

This distinction must be explicit before claiming equivalence with a standard
deep handler calculus.

## 10. Relationship to the current trace model

The quantitative system should be derived as an abstraction of ordered trace
languages, not introduced as an unrelated semantics.

For a trace $m$, let

$$
\mathsf{count}(m)(\Delta)
$$

be the number of $Delta$ tokens in $m$. For a language $L$, define

$$
\alpha_{\mathrm{count}}(L)(\Delta)
=
\sup_{m\in L}\mathsf{count}(m)(\Delta).
$$

Then

$$
\mathsf{count}(mn)
=
\mathsf{count}(m)+\mathsf{count}(n),
$$

and union becomes pointwise maximum. The main abstraction obligation is

$$
\alpha_{\mathrm{count}}
(\mathsf{Catch}_{\Delta,K}(L))
\leq
\Psi_{\Delta,\alpha(K)}
(\alpha_{\mathrm{count}}(L)),
$$

with

$$
\Psi_\Delta(n,k)=(n-1)^++k.
$$

Here $\mathsf{Catch}$ is a new first-matching trace transformer, distinct from
the current first-free-head transformer $\Phi$.

## 11. Abstraction ladder

The possible sequence of static abstractions is:

```text
ordered trace languages
        |
        v
per-interface occurrence bounds N_infinity^D
        |
        v
affine grades {0, 1, omega}
        |
        v
unordered may-effect rows
```

Each step forgets information:

| Grade | Retained information |
|---|---|
| trace language | order, first head, interface, multiplicity |
| count vector | interface and pathwise multiplicity |
| $\{0,1,\omega\}$ | absent, affine, unrestricted |
| row | possible interface only |

The desired theorem at each step is a sound abstract-handler simulation.

## 12. Proposed investigation order

1. Define a single-interface $\mathbb N_\infty$-graded calculus.
2. Prove return, sequencing, branch, and subeffect laws.
3. Define catch-once and prove

   $$
   n\mapsto(n-1)^++k.
   $$

4. Prove operational/tree adequacy and base conservativity.
5. Generalize to count vectors $\mathbb N_\infty^{\mathcal D}$.
6. Verify that transparent other-interface forwarding preserves the decrement.
7. Add fuel $m$ and prove $(n-m)^+$.
8. Compare the $m=\omega$ limit with deep handlers.
9. Prove abstraction from the current ordered trace-language semantics.
10. Investigate intervals $[\ell,u]$ if must-occurrence information becomes
    useful.

## 13. Candidate theorem

> An exactly-once-resuming catch handler with fuel $m$ transparently traverses
> nonmatching algebraic effects, processes at most $m$ matching occurrences, and
> transforms the pathwise occurrence upper bound of $Delta$ from $n$ to
> $(n-m)^+$, plus the effects introduced by executed clauses.

This theorem is not yet proved. It defines a separate later branch of the
research rather than modifying the current main result.

## 14. Main unresolved questions

- Is $mathbb N_\infty^{\mathcal D}$ sufficient for open higher-order programs,
  or is a quantitative continuation usage semiring also needed?
- How should clause effects be multiplied when up to $m$ clauses execute?
- Does the fuel-$\omega$ construction satisfy the standard deep-handler
  equations?
- Can catch-once coexist with dynamically generated effect instances?
- What finite inference syntax gives principal quantitative grades?
- Which abstraction theorem precisely relates the current $\Phi$ and the new
  first-matching catch transformer?

These questions are intentionally deferred until the current first-free-head
development has reached a stable stopping point.
