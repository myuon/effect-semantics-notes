# Exception handler interaction v2

## Status

**Concrete operational instance with an existing base handler.** This instance
tests more than an exception monad: the base language already contains `try`,
so old and newly added handlers may be nested in either order.

## 1. Base exception language

Fix an exception value type $X$.  Add an abortive base primitive, polymorphic in
its computation result type,

$$
\operatorname{raise}_A:X\to A.
$$

We normally omit the result subscript.  Equivalently one may use
$\operatorname{raise}:X\to0$ together with empty-type elimination; the
polymorphic presentation keeps clause examples uncluttered.

and the base construct

$$
\mathbf{try}\ M\ \mathbf{with}\ x\Rightarrow N.
$$

The characteristic rules are

$$
\mathbf{try}\ (\operatorname{return}V)\ \mathbf{with}\ x\Rightarrow N
\longrightarrow
\operatorname{return}V,
\tag{X-Ret}
$$

$$
\mathbf{try}\ E^X[\operatorname{raise}(e)]\
\mathbf{with}\ x\Rightarrow N
\longrightarrow
N[e/x].
\tag{X-Raise}
$$

$E^X$ contains no intervening base `try`.  A free request is not an exception;
when it is forwarded through `try`, its continuation retains the pending base
exception handler.

For the projected new free row, `raise` and `try` are base constructs and do
not introduce a new interface label.

## 2. Outcome decomposition

The base adds a fourth observable outcome.

:::{prf:theorem} Exception configuration decomposition
:label: thm-exn-decomposition-v2

Every closed, well-typed computation is uniquely one of:

1. a return;
2. an internal step;
3. an unhandled base exception $E^X[\operatorname{raise}(e)]$;
4. an unhandled new free request
   $E^\Delta[\operatorname{op}_{\Delta,i}(V)]$.
:::

:::{prf:proof}
Induction on the unique CBV context.  A nearest base `try` turns an exposed
raise into `X-Raise`; otherwise the raise propagates outward.  A nearest
matching free handler turns its request into `H-Op-Deep`; otherwise the request
propagates through nonmatching free handlers and base `try` frames.  Nominal
matching and distinct syntactic heads make the four cases disjoint.
:::

One-step reduction remains deterministic.

## 3. The six common calculations

The conditional, nonmatching-forward, two-matching-request, distinct-handler,
and base-only calculations behave as before until an exception is raised.

The effectful-clause case is now:

$$
\operatorname{ask}(u,k)\mapsto\operatorname{raise}(e).
$$

It discards the resumption and aborts.  The free Ask row is eliminated, but the
base exception outcome remains.  Thus free-effect elimination does not mean
elimination of effects introduced by the interpretation.

A base-only raise under an identity-return free handler remains an unhandled
base raise:

$$
H_A(\operatorname{raise}(e))
$$

does not select an Ask clause.

## 4. The key nesting-order example

Let $h_A^X$ handle Ask by raising $e$ without resuming.

### Base try outside the free handler

$$
\mathbf{try}\
\left(H_A^X(\operatorname{ask}())\right)
\ \mathbf{with}\ x\Rightarrow\operatorname{return}\mathsf{false}.
$$

The Ask clause is executed inside the surrounding `try`, so its raise is caught
and the result is `false`.

### Base try inside the free handler

$$
H_A^X\left(
\mathbf{try}\ \operatorname{ask}()\
\mathbf{with}\ x\Rightarrow\operatorname{return}\mathsf{false}
\right).
$$

The inner `try` does not match Ask.  The outer free handler captures the request
through a transparent context containing that `try`.  The captured `try`
belongs to the resumption, but the Ask clause executes outside the captured
context.  Because the clause discards the resumption and raises directly, the
inner `try` never sees this exception.  The result is an unhandled raise $e$.

Therefore

$$
\mathbf{try}\circ H_A^X
\neq
H_A^X\circ\mathbf{try}.
$$

This is a semantic interaction between old and new handlers, not a failure of
unordered free rows.

## 5. Forwarding through an old handler

Consider

$$
\mathbf{try}\
(\operatorname{ping}();\operatorname{raise}(e))
\ \mathbf{with}\ x\Rightarrow\operatorname{return}().
$$

At the Ping request, the outward request continuation contains the pending
`try`.  If an outer Ping handler resumes it, the later raise is caught.  Thus
old base handlers and new free handlers obey the same general forwarding
principle: a nonmatching handler remains in the captured continuation.

## 6. Free-row metatheory

:::{prf:theorem} Exception free-row safety
:label: thm-exn-row-safety-v2

The extended Exception instance satisfies free-row preservation and
effect-aware progress with separate base-raise and free-request outcomes.  In
particular, an empty new free row prevents unhandled new requests but does not
prevent an unhandled base exception.
:::

:::{prf:proof}
Substitution and free-handler cases are unchanged.  `raise` has no internal
step unless caught by a `try`; `X-Raise` substitutes into the catch body.
Typing inversion classifies an exposed `raise` as an allowed base outcome and
an exposed free request by membership in the new row.
:::

:::{prf:theorem} Exception-instance deep elimination
:label: thm-exn-deep-elimination-v2

An exhaustive $\Delta$ handler whose outward new row excludes $\Delta$
prevents unhandled $\Delta$ requests from escaping.  The handled computation
may still return, raise a base exception, or expose another free interface.
:::

## 7. Conservativity

Old terms containing only `raise`, `try`, and ordinary constructs have exactly
their old reductions and observations under the language extension.

Wrapping an old term in an identity-return free handler preserves returns and
unhandled base exceptions, provided its free operation clauses are unreachable.
As before, a nonidentity return clause can change an old successful return.

## 8. Base facts used

| Result | Exception-specific facts used |
|---|---|
| decomposition | raise is a distinct aborting head; nearest `try` is unique |
| determinism | deterministic catch selection and CBV contexts |
| row preservation | raise/try are silent in the new row |
| deep elimination | free preservation/progress; base raise remains separate |
| conservativity | new free rules do not rewrite old syntax |
| interaction result | handler clauses execute outside captured continuation contexts |

The last fact is not supplied by monad laws alone.  It is a scoping choice in
the operational semantics of handlers.
