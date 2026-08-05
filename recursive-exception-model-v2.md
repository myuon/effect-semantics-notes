# Recursive Exception model v2

## Status

**Third concrete instance of `RecursiveBaseAdequacy`.**  It adds an abortive
base outcome and checks the scope interaction between old `try` and new deep
handlers in the presence of divergence.

## 1. Partial Exception base

Let $E$ be a countably based exception domain.  Use

$$
T_\bot A=(A+E)_\bot.
$$

The three base observations are:

$$
\bot,
\qquad
\mathsf{ret}(a),
\qquad
\mathsf{raise}(e).
$$

Bottom represents boundary-free divergence and is distinct from a raised
exception.

## 2. Recursive Exception resumption

For a free row $\rho$, solve

$$
\mathsf{CXTree}_\rho A
\cong
\left(
A+E+
\sum_{\Delta\in\rho}
\sum_i
P_i\times[R_i\to_c\mathsf{CXTree}_\rho A]
\right)_\bot.
$$

The constructors are bottom, return, base raise, and nominal free request.
The functor is locally continuous and admits the same bilimit/projective
construction as Writer and State.

## 3. Monad structure

Bind is strict at bottom, substitutes at return, propagates raise, and maps
pointwise through a free-request continuation:

$$
\bot\mathbin{\gg=}f=\bot,
$$

$$
\mathsf{ret}(a)\mathbin{\gg=}f=f(a),
$$

$$
\mathsf{raise}(e)\mathbin{\gg=}f=\mathsf{raise}(e),
$$

$$
\mathsf{req}(\delta,i,p,k)\mathbin{\gg=}f
=\mathsf{req}(\delta,i,p,\lambda r.k(r)\mathbin{\gg=}f).
$$

:::{prf:theorem} Recursive Exception row monad
:label: thm-recursive-exception-monad-v2

$\mathsf{CXTree}$ is a pointed locally continuous row-refined monad, embeds the
partial Exception base at empty free row, and interprets recursive functions by
least fixed points.
:::

## 4. Old `try`

For a continuous exception clause

$$
h:E\to\mathsf{CXTree}_\rho A,
$$

define

$$
\mathsf{Try}_h(\bot)=\bot,
$$

$$
\mathsf{Try}_h(\mathsf{ret}(a))=\mathsf{ret}(a),
$$

$$
\mathsf{Try}_h(\mathsf{raise}(e))=h(e),
$$

$$
\mathsf{Try}_h(\mathsf{req}(\delta,i,p,k))
=\mathsf{req}(\delta,i,p,\lambda r.\mathsf{Try}_h(k(r))).
$$

Thus an unhandled free request passes through `try` while retaining the pending
`try` in its continuation.

## 5. New deep handler

The free-handler functional has four source cases:

$$
\Phi_h(g)(\bot)=\bot,
$$

$$
\Phi_h(g)(\mathsf{ret}(a))=r(a),
$$

$$
\Phi_h(g)(\mathsf{raise}(e))=\mathsf{raise}(e),
$$

and matching/forwarding request equations as before.  Define

$$
H_{\Delta,h}=\mathsf{lfp}(\Phi_h).
$$

A base exception already raised while evaluating the handled source propagates
outward.  A matching operation clause executes in the context outside the
captured resumption.

## 6. Scope calculation

In

```text
try (handle M with hDelta) with hE
```

the outer `try` is applied to the complete result of $H_{\Delta,h}$.  Therefore
a raise produced directly by a free-operation clause is caught by $h_E$.

In

```text
handle (try M with hE) with hDelta
```

a free request from $M$ is forwarded through `try`, retaining `try` only inside
the request continuation.  The outer free handler then runs its matching clause
outside that continuation.  A raise produced directly by this clause is not
caught by $h_E$ unless the clause invokes the resumption and the raise occurs
inside the resumed computation.

Consequently,

$$
\mathsf{Try}_{h_E}\circ H_{\Delta,h}
\neq
H_{\Delta,h}\circ\mathsf{Try}_{h_E}
$$

in general, exactly as in the recursion-free Exception calculation.

## 7. Divergence interaction

Both `try` and the free handler are strict:

$$
\mathsf{Try}_{h_E}(\bot)=\bot,
\qquad
H_{\Delta,h}(\bot)=\bot.
$$

They do not turn silent divergence into return or raise.  A recursively
generated infinite sequence of handled requests may also have least solution
bottom when no outward boundary is produced.
