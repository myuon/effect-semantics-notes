# Recursive State model v2

## Status

**Second concrete instance of `RecursiveBaseAdequacy`.**  It tests whether the
package works without Writer-prefix normalization and fixes global sequential
state across recursive and multi-shot resumptions.

## 1. Partial State base

Let $S$ be a countably based state domain; for the first instance it may be a
flat countable set.  The recursive base computation monad is

$$
T_\bot A=[S\to_c(A\times S)_\bot].
$$

Bottom at input $s$ means that execution from $s$ reaches no return/free-request
boundary.  The model records final state for terminating phases but not the
sequence of transient states in a divergent phase.

## 2. Recursive State resumption equation

Define

$$
\mathsf{CSTree}_\rho A
\cong
\left[
S\to_c
\left(
A\times S
+
\sum_{\Delta\in\rho}
\sum_i
P_i\times S\times
[R_i\to_c\mathsf{CSTree}_\rho A]
\right)_\bot
\right].
$$

For an initial state $s$, the observation is one of:

$$
\bot,
\qquad
\mathsf{ret}(a,s'),
\qquad
\mathsf{req}(\Delta,i,p,s',k).
$$

The request records the state $s'$ reached before issuing the free operation.
Its continuation $k(r)$ is again a state transformer; it does not have a fixed
starting state until the resumption is invoked.

The defining endofunctor is locally continuous and has the same bilimit
construction as recursive Writer, now with an additional outer continuous-
function space $[S\to_c-]$.

## 3. Return and bind

Return is

$$
\eta(a)(s)=\mathsf{ret}(a,s).
$$

Bind is strict at a boundary-divergent input:

$$
(t\mathbin{\gg=}f)(s)=
\begin{cases}
\bot & t(s)=\bot,\\
f(a)(s') & t(s)=\mathsf{ret}(a,s'),\\
\mathsf{req}(\delta,i,p,s',
  \lambda r.k(r)\mathbin{\gg=}f)
&t(s)=\mathsf{req}(\delta,i,p,s',k).
\end{cases}
$$

This threads global state through completed base phases.  A residual request
suspends before its response is known; after a response, the resumed tree is
run from the state current at the point where the resumption is invoked.

:::{prf:theorem} Recursive State row monad
:label: thm-recursive-state-monad-v2

$\mathsf{CSTree}$ is a pointed locally continuous row-refined monad with
weakening by row inclusion and least-fixed-point interpretation of recursive
functions.
:::

The proof is pointwise in the initial state and uses the same finite projections
as the Writer domain.

## 4. State primitives

For total global State:

$$
\llbracket\mathsf{get}\rrbracket(s)=\mathsf{ret}(s,s),
$$

$$
\llbracket\mathsf{put}(s')\rrbracket(s)
=\mathsf{ret}((),s').
$$

Both are continuous for flat/countably based state and satisfy the direct
machine transitions exactly.

## 5. Recursive deep handler

For continuous return and operation clauses, define a functional $\Phi_h$ on
continuous maps

$$
g:\mathsf{CSTree}_{\rho\cup\{\Delta\}}A
\to_c\mathsf{CSTree}_\omega C.
$$

Pointwise at initial state $s$:

$$
\Phi_h(g)(t)(s)=
\begin{cases}
\bot&t(s)=\bot,\\
r(a)(s')&t(s)=\mathsf{ret}(a,s'),\\
c_i(p,\lambda x.g(k(x)))(s')
&t(s)=\mathsf{req}(\Delta,i,p,s',k),\\
\mathsf{req}(\delta,i,p,s',\lambda x.g(k(x)))
&t(s)=\mathsf{req}(\delta,i,p,s',k),\ \delta\neq\Delta.
\end{cases}
$$

Set

$$
H_{\Delta,h}=\mathsf{lfp}(\Phi_h).
$$

The matching clause starts in $s'$, the state at the request.  If it executes
`put` and then invokes the resumption, the resumed computation receives that
new current state.  Nothing restores the request-time snapshot.

## 6. Multi-shot global State

Suppose a clause executes

```text
put(1);
k(());
put(2);
k(())
```

The first resumption starts from state `1`.  After it and the intervening clause
computation finish, the second starts from the state established at its own
invocation.  This is global sequential State, not backtracking State.

The semantic clause above enforces this because a resumption is a State
computation, not a pair containing a permanently captured starting state.

## 7. Discharge

If $\Delta\notin\omega$, the least-fixed-point handler maps into
$\mathsf{CSTree}_\omega$.  Hence no finite observation from any initial state
exposes an unhandled $\Delta$.  Divergence remains possible and state changes
before divergence are not retained by this coarse model.
