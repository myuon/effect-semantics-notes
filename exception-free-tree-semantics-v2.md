# Exception free-tree semantics v2

## Status

**Concrete exception-plus-free tree semantics and paper correspondence.**

## 1. Exception-resumption trees

The carrier is the free-operation transformer over exceptions:

$$
\mathsf{XTree}_\Sigma A
\cong
A+X+
\sum_{\Delta,i}
P_i\times(R_i\to\mathsf{XTree}_\Sigma A).
$$

Write constructors

$$
\mathsf{Ret}(a),
\qquad
\mathsf{Raise}(e),
\qquad
\mathsf{Req}(\Delta,i,p,k).
$$

## 2. Monad and primitives

Bind is

$$
\mathsf{Ret}(a)\mathbin{\gg=}f=f(a),
$$

$$
\mathsf{Raise}(e)\mathbin{\gg=}f=\mathsf{Raise}(e),
$$

$$
\mathsf{Req}(\Delta,i,p,k)\mathbin{\gg=}f
=
\mathsf{Req}(\Delta,i,p,\lambda r.k(r)\mathbin{\gg=}f).
$$

The monad laws follow structurally.  Interpret

$$
\llbracket\operatorname{raise}_A(e)\rrbracket=\mathsf{Raise}(e)
$$

and free operations by one `Req` node with a pure response continuation.

## 3. Existing base `try`

For catch body $c:X\to\mathsf{XTree}_\rho A$, define

$$
\mathsf{Try}_c(\mathsf{Ret}(a))=\mathsf{Ret}(a),
$$

$$
\mathsf{Try}_c(\mathsf{Raise}(e))=c(e),
$$

$$
\mathsf{Try}_c(\mathsf{Req}(\Delta,i,p,k))
=
\mathsf{Req}(\Delta,i,p,\lambda r.\mathsf{Try}_c(k(r))).
$$

The third equation says that `try` remains pending while a nonmatching free
request is forwarded.

## 4. New deep free handler

For free handler clauses $r,c_i$, define

$$
H_{\Delta,h}(\mathsf{Ret}(a))=r(a),
$$

$$
H_{\Delta,h}(\mathsf{Raise}(e))=\mathsf{Raise}(e),
$$

$$
H_{\Delta,h}(\mathsf{Req}(\Delta,i,p,k))
=
c_i(p,\lambda x.H_{\Delta,h}(k(x))),
$$

$$
H_{\Delta,h}(\mathsf{Req}(\Gamma,j,p,k))
=
\mathsf{Req}(\Gamma,j,p,\lambda x.H_{\Delta,h}(k(x)))
\quad(\Gamma\neq\Delta).
$$

A base raise is forwarded as an aborting base outcome.  A raise produced by a
free clause is part of the clause result and is not recursively fed through
the captured base `try` unless that `try` syntactically surrounds the free
handler.

## 5. One-step soundness and conditional adequacy

:::{prf:theorem} Exception-tree one-step soundness
:label: thm-xtree-step-sound-v2

Every ordinary, base-exception, or free-handler reduction preserves
$\mathsf{XTree}$ denotation.
:::

:::{prf:proof}
Ordinary cases use substitution and monad laws.  `X-Ret` and `X-Raise` are the
first two equations of $\mathsf{Try}$.  Free handler cases are the equations of
$H$.  Forwarding through either kind of handler is structural recursion on the
request continuation.
:::

:::{prf:theorem} Exception-tree adequacy, conditional form
:label: thm-xtree-adequacy-v2

Assuming a closed first-order computation reaches an observable outcome, its
operational return, base raise, or free request agrees exactly with the outer
constructor of its $\mathsf{XTree}$ denotation, and conversely.
:::

The proof iterates one-step soundness and uses the four-way operational
decomposition.  The three observable constructors are disjoint.

## 6. Nesting order denotationally

Let the Ask clause be

$$
c_A(p,k)=\mathsf{Raise}(e)
$$

and let the base catch map every exception to
$\mathsf{Ret}(\mathsf{false})$.

Then

$$
\mathsf{Try}_c
\left(H_A(\mathsf{Req}(A,\mathsf{ask},(),k))\right)
=
\mathsf{Ret}(\mathsf{false}),
$$

but

$$
H_A\left(
\mathsf{Try}_c(\mathsf{Req}(A,\mathsf{ask},(),k))
\right)
=
\mathsf{Raise}(e).
$$

In the second equation, $\mathsf{Try}_c$ is pushed only into the request
continuation; $H_A$ replaces the request by a clause that discards that
continuation.  This exactly reproduces the operational scope example.

## 7. What Exception adds to the comparison

Writer and State base layers always reach return or a free request after a
primitive step.  Exception adds an aborting base observation that bypasses the
ordinary continuation.

The common free-handler construction therefore needs not merely a monad, but a
way to distinguish:

- base return available to the handler return clause;
- new free request available to the new handler;
- base-specific nonreturn outcomes that must be propagated.

In a free-transformer presentation this distinction appears in the base monad
outside the free request layer.  In an operational package it appears as a
base-machine outcome interface.
