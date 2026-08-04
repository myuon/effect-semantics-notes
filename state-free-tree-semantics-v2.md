# State free-tree semantics v2

## Status

**Concrete State-plus-free denotation and paper correspondence.** Adequacy is
termination-conditional for the same reason as in the Writer instance.

## 1. State-resumption trees

The appropriate carrier is the free-operation transformer over the global
State monad:

$$
\mathsf{STree}_\Sigma A
\cong
S\to\left(
A\times S
+
\sum_{\Delta,i}
P_i\times S\times(R_i\to\mathsf{STree}_\Sigma A)
\right).
$$

Running a tree at state $s$ either:

- returns a value and final state;
- exposes a free request, the state reached before that request, and a
  continuation that accepts a response and then a state at resumption time.

Write the observations as

$$
\mathsf{Ret}(a,s')
$$

and

$$
\mathsf{Req}(\Delta,i,p,s',k).
$$

The continuation $k(r):\mathsf{STree}_\Sigma A$ is still a state computation;
it is not closed over one fixed state.  This realizes global sequential state.

## 2. Monad structure

Unit is

$$
\eta(a)(s)=\mathsf{Ret}(a,s).
$$

Bind is

$$
(t\mathbin{\gg=}f)(s)=
\begin{cases}
f(a)(s')
&t(s)=\mathsf{Ret}(a,s'),\\
\mathsf{Req}(\Delta,i,p,s',\lambda r.k(r)\mathbin{\gg=}f)
&t(s)=\mathsf{Req}(\Delta,i,p,s',k).
\end{cases}
$$

:::{prf:theorem} State-resumption trees form a monad
:label: thm-stree-monad-v2

The operations above satisfy the monad laws.  Restricting request labels to
rows gives

$$
\mathsf{STree}_\rho A\times
(A\to\mathsf{STree}_\sigma C)
\to
\mathsf{STree}_{\rho\cup\sigma}C.
$$
:::

:::{prf:proof}
Extensionality in the initial state, followed by cases on the first
observation.  Return cases reduce to ordinary State threading; request cases
use the induction hypothesis pointwise in response continuations.
:::

## 3. Base and free primitives

$$
\llbracket\operatorname{get}()\rrbracket(s)
=
\mathsf{Ret}(s,s),
$$

$$
\llbracket\operatorname{put}(s')\rrbracket(s)
=
\mathsf{Ret}((),s'),
$$

$$
\llbracket\operatorname{op}_{\Delta,i}(V)\rrbracket(s)
=
\mathsf{Req}
(\Delta,i,\llbracket V\rrbracket,s,
\lambda r.\eta(r)).
$$

Sequencing is tree bind.  This interpretation is sound for the projected free
row because `get` and `put` introduce no free request node.

## 4. Deep handler

Let return and operation clauses denote State-tree computations

$$
r:A\to\mathsf{STree}_\omega C,
$$

$$
c_i:P_i\to(R_i\to\mathsf{STree}_\omega C)
\to\mathsf{STree}_\omega C.
$$

Define $H_{\Delta,h}(t)$ extensionally in the current state:

$$
H_{\Delta,h}(t)(s)=
\begin{cases}
r(a)(s')
&t(s)=\mathsf{Ret}(a,s'),\\
c_i(p,\lambda x.H_{\Delta,h}(k(x)))(s')
&t(s)=\mathsf{Req}(\Delta,i,p,s',k),\\
\mathsf{Req}
(\Gamma,j,p,s',\lambda x.H_{\Delta,h}(k(x)))
&t(s)=\mathsf{Req}(\Gamma,j,p,s',k),\ \Gamma\neq\Delta.
\end{cases}
$$

The clause begins in the state $s'$ reached at the request.  A resumption is a
State computation and therefore begins in whichever state is current when the
clause invokes it.

:::{prf:theorem} State denotational deep elimination
:label: thm-stree-elimination-v2

If every clause tree and residual row is $\Delta$-free, then

$$
H_{\Delta,h}:
\mathsf{STree}_{\rho\cup\{\Delta\}}A
\to
\mathsf{STree}_\omega C
$$

produces no $\Delta$ request for any initial state.
:::

:::{prf:proof}
Extensional structural recursion on the observation tree.  Matching requests
are replaced; nonmatching request continuations are recursively handled.
:::

## 5. Operational soundness

Interpret a configuration by applying the term tree to its current state:

$$
\llbracket\langle s,M\rangle\rrbracket_{\mathrm{cfg}}
=
\llbracket M\rrbracket(s).
$$

:::{prf:theorem} State one-step soundness
:label: thm-stree-step-sound-v2

If

$$
\langle s,M\rangle\to\langle s',M'\rangle,
$$

then

$$
\llbracket M\rrbracket(s)=\llbracket M'\rrbracket(s').
$$
:::

:::{prf:proof}
Ordinary rules use substitution and monad laws.  `S-Get` and `S-Put` are their
defining equations.  Handler return and matching use the corresponding cases
of $H_{\Delta,h}$; nonmatching forwarding is its request case.  Context closure
uses compositionality of State-tree bind and handler interpretation.
:::

## 6. Conditional adequacy

:::{prf:theorem} State tree adequacy, conditional form
:label: thm-stree-adequacy-v2

For a closed first-order computation whose deterministic evaluation reaches a
return or unhandled free request:

- operational return $(a,s')$ agrees exactly with
  $\mathsf{Ret}(a,s')$;
- an exposed request agrees with the root $\mathsf{Req}$ label, parameter,
  reached state, and continuation denotation.
:::

:::{prf:proof}
Iterate one-step soundness and use State configuration decomposition.  Return
and request observations are disjoint.  The reverse direction uses the stated
termination assumption.
:::

## 7. Multi-shot state equation

Suppose a matching clause sequentially invokes a resumption twice.  If the
first invocation transforms state by relation $R$ and the second by the same
relation, then global sequential State composes them as

$$
R;R.
$$

It does not interpret both invocations from one captured snapshot.  For the
increment example:

$$
n\mapsto n+1\mapsto n+2.
$$

A backtracking interpretation would instead clone the state at the request and
combine two separate branches.  That is a different distributive choice, not a
different free-row typing rule.

## 8. Exact relational-grade obstruction

:::{prf:theorem} No exact State transition from row data alone
:label: thm-row-only-state-obstruction-v2

There is no transformer that uses only an exact input transition relation, an
unordered free row, and one clause transition relation to compute the exact
handled transition of every program.
:::

:::{prf:proof}
Use zero, one, and two Ask requests, all widened to row
$\{\mathsf{Ask}\}$, and the incrementing clause.  With identity input base
transition and the same single-invocation successor relation, the handled
relations are identity, successor, and successor composed with itself.
:::

As with Writer, reflexive-transitive closure gives a safe but less precise
answer.  Counts or intensional trees recover more precision.

## 9. Comparison with Writer

The common structural pattern is already visible:

$$
\text{run base behavior to return or free request}
\longrightarrow
\text{inspect the free head}
\longrightarrow
\text{continue in the base model}.
$$

Writer realizes “run base behavior” by multiplying a prefix segment.  State
realizes it by passing a state into the computation and receiving a reached
state.  The shared handler recursion is on the exposed free structure, not on
the internal representation of the base monad.

This suggests a free-transformer or resumption interface, but two instances are
not yet enough to choose the final abstraction.  Exception is the next test
because its base computation may abort before exposing either return or free
request.
