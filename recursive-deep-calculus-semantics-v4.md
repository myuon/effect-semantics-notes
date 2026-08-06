# Recursive deep calculus and denotational reconstruction v4

## Status

**Fixed Chapter II calculus and semantic candidate.**  It extends Chapter I
with general recursive functions and replaces the one-boundary matcher by a
conventional exhaustive deep handler.

## 1. Recursive source construct

Add

```text
let rec f(x) = M in N
```

with an effectful function type

$$
f:A\to(B!\rho).
$$

The body $M$ is checked at $B!\rho$ under $f:A\to(B!\rho)$ and $x:A$.
The continuation $N$ is checked under the same recursive function.  Recursion
does not add a distinguished free-effect label: it may repeat any effect in
$\rho$, or diverge while the outward row is empty.

Operational unfolding is the usual CBV rule.  Unlike Chapter I, progress does
not imply termination.

## 2. Deep handler syntax and typing

An exhaustive handler for interface $\Delta$ is

$$
h=
\{\mathsf{return}(x)\mapsto H_{\mathsf{ret}};
  \mathsf{op}_i(p,k)\mapsto H_i\}_{i\in I_\Delta}.
$$

Suppose the handled computation has row $\rho\cup\{\Delta\}$, with
$\Delta\notin\rho$.  Choose an output row $\omega$ such that
$\rho\subseteq\omega$.  Type the clauses by

$$
\Gamma,x:A\vdash H_{\mathsf{ret}}:C!\omega
$$

and

$$
\Gamma,p:P_i,k:R_i\to(C!\omega)\vdash H_i:C!\omega.
$$

Then

$$
\Gamma\vdash
\mathsf{handle}_\Delta M\ \mathsf{with}\ h:C!\omega.
$$

The resumption $k$ is an ordinary function and may be ignored, called once or
called more than once.  Every call reinstalls the same handler.  If the return
and operation clauses are $\Delta$-free, we may choose
$\Delta\notin\omega$ and genuinely discharge the interface from the outward
may-row.

This typing says nothing about termination and nothing about the exact old base
grade after a multi-shot clause.

## 3. Operational deep equations

For returns,

$$
\mathsf{handle}_\Delta(\mathsf{return}\;V,h)
\longrightarrow H_{\mathsf{ret}}[V/x].
\tag{D-Ret}
$$

For a matching request exposed in a $\Delta$-transparent context $E$,

$$
\begin{aligned}
&\mathsf{handle}_\Delta(E[\mathsf{op}_{\Delta,i}(V)],h)\\
&\quad\longrightarrow
H_i\left[V/p,
\left(\lambda r.\mathsf{handle}_\Delta(E[\mathsf{return}\;r],h)\right)/k
\right].
\end{aligned}
\tag{D-Match}
$$

For $Gamma\neq\Delta$, forward the request while retaining the pending
handler in its continuation:

$$
\begin{aligned}
&\mathsf{handle}_\Delta(E[\mathsf{op}_{\Gamma,j}(V)],h)\\
&\quad\leadsto
\mathsf{op}_{\Gamma,j}
\left(V;
  r\mapsto\mathsf{handle}_\Delta(E[\mathsf{return}\;r],h)
\right).
\end{aligned}
\tag{D-Other}
$$

The continuation notation in the target is metatheoretic; source operations
remain ordinary expressions of their response type.

## 4. Recursive resumption carrier

Let

$$
\Sigma_\rho X
=
\coprod_{\Delta\in\rho}
\coprod_{i\in I_\Delta}
P_i\times(R_i\to X).
$$

Let $T$ be the pointed/order-enriched model of old base computation.  The
semantic candidate is a selected solution of

$$
\mathsf{R}_{T,\rho}A
\cong
T\bigl(A+\Sigma_\rho(\mathsf{R}_{T,\rho}A)\bigr).
\tag{R-Domain}
$$

Depending on the base category, this may be presented as:

- a minimal recursive domain solution;
- a coinductive generalized resumption;
- a guarded final coalgebra;
- the limit of finite approximants.

These presentations are not identified without proof.  For the least-fixed-point
instances below, we use pointed $\omega$-cpos, locally continuous constructors
and the minimal solution.

Return, bind and row weakening make $\mathsf{R}_{T,-}$ a row-refined monad.
The base embedding is the complete-Elgot/continuous monad morphism

$$
j:T A\to\mathsf{R}_{T,\varnothing}A.
$$

When $T$ is a complete Elgot monad and the required coalgebras exist, the known
resumption theorem supplies iteration on $\mathsf{R}_{T,\rho}$ extending that
of $T$.

## 5. Recursive-function denotation

For a recursive body denoting a continuous functional

$$
\Phi:(A\to\mathsf{R}_{T,\rho}B)
\to(A\to\mathsf{R}_{T,\rho}B),
$$

interpret the recursive function by

$$
\operatorname{lfp}(\Phi)
=
\bigsqcup_{n<\omega}\Phi^n(\bot).
$$

Equivalently, in a complete-Elgot presentation, use the selected iteration
operator.  The theorem must require these choices to agree on source-definable
recursive equations; this agreement is not automatic from monad laws.

## 6. Deep-handler denotation

The handler is the selected strict continuous map

$$
\mathcal H_h:
\mathsf{R}_{T,\rho\cup\{\Delta\}}A
\to
\mathsf{R}_{T,\omega}C
$$

satisfying:

1. $\mathcal H_h(\bot)=\bot$;
2. returns use $H_{\mathsf{ret}}$;
3. matching requests use $H_i$ with
   $k_h(r)=\mathcal H_h(k(r))$;
4. nonmatching requests are rebuilt with continuation
   $\mathcal H_h\circ k$;
5. old base structure is preserved through the supplied base action.

The recursive calls in both operation cases are the semantic form of deep
reinstallation.  If clause denotations are continuous, these equations define
a continuous functional on candidate handler maps.  A minimal-domain recursion
principle, guarded corecursion or selected least fixed point supplies
$\mathcal H_h$.

## 7. What the effect row means with recursion

The row remains a may-property:

$$
\Delta\in\rho
\quad\text{means that a finite execution prefix may expose }\Delta.
$$

It does not imply that the request is ever reached, or bound the number of
times it occurs.  A recursive cycle can make the number of occurrences
unbounded.

After an exhaustive deep handler with $\Delta$-free clauses, the target row may
exclude $\Delta$.  The correct dynamic reading is:

> no finite execution prefix of the handled computation exposes an unhandled
> $\Delta$ request outside the handler.

The program may return, raise an old exception, diverge silently, or produce an
infinite old-effect trace.  Discharge is a safety statement, not termination.
