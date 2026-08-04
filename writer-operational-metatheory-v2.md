# Writer operational metatheory v2

## Status

**Paper proofs for the concrete Writer instance.** These results validate the
direct semantics before a denotational model is introduced.  They are not yet
machine checked.

## 1. Fixed instance

We use [Common free-handler calculus v2](common-free-handler-calculus-v2.md)
with the Writer configurations and transitions of [Writer deep-handler
examples v2](writer-deep-handler-examples-v2.md).

Let $(W,\cdot,\epsilon)$ be an arbitrary monoid.  A configuration is

$$
\langle w,M\rangle.
$$

The only primitive Writer transition is

$$
\langle w,\operatorname{tell}(a)\rangle
\longrightarrow
\langle w\cdot a,\operatorname{return}()\rangle.
$$

The result below does not assume that $W$ is commutative, cancellative, or
idempotent.

## 2. Administrative assumptions made explicit

The common calculus page suppresses products, sums, and ordinary congruence
rules.  For the proofs here we fix the following standard details.

1. Evaluation is left-to-right fine-grain CBV.
2. Only computations occur in the evaluation hole.
3. Reduction is closed under the unique ordinary evaluation context.
4. Handler clauses are finite and contain exactly one clause for every
   operation of their named interface.
5. Interface and operation names have decidable equality.
6. Alpha-equivalent terms and contexts are identified.
7. The Writer transition is deterministic.

No assumption is made about how many times a clause uses its resumption.

## 3. Requests and blocked configurations

For a free operation

$$
\operatorname{op}_{\Delta,i}(V),
$$

a top-level unhandled request is represented by a decomposition

$$
M=E^\Delta[\operatorname{op}_{\Delta,i}(V)],
$$

where $E^\Delta$ contains no handler for $\Delta$ between the operation and the
top level.

Its request continuation is the meta-level function

$$
K_{E^\Delta}=\lambda y.E^\Delta[\operatorname{return}y].
$$

We write

$$
\langle w,M\rangle
\Downarrow_{\mathrm{req}}
(w;\Delta,i,V,K_{E^\Delta})
$$

for this decomposition.  It does not perform a transition.  It exposes why a
well-typed open-effect computation may be unable to take an internal step.

## 4. Unique active-position lemma

:::{prf:lemma} Unique active position
:label: lem-writer-unique-position

For every closed, well-typed computation $M$, exactly one of the following syntactic
positions is active:

1. $M=\operatorname{return}V$;
2. $M=E[R]$ for a unique ordinary redex $R$;
3. $M=E^\Delta[\operatorname{op}_{\Delta,i}(V)]$ for a unique first free
   request and its maximal transparent context.
:::

:::{prf:proof}
By structural induction on $M$ and its unique CBV evaluation context.

The only nonstandard case is

$$
M=\operatorname{handle}_{\Gamma}N\operatorname{with}h.
$$

Apply the induction hypothesis to $N$.

- If $N$ returns, `H-Ret` is the unique active redex.
- If $N$ takes an ordinary or Writer step, that step lifts uniquely through the
  handler context.
- If $N$ exposes a $\Delta$ request and $\Delta=\Gamma$, exhaustiveness makes
  `H-Op-Deep` the unique redex.
- If $\Delta\neq\Gamma$, the handler is a valid additional frame of the maximal
  $\Delta$-transparent context, so the same request is exposed outward.

A handler for the same interface cannot be crossed by a transparent context.
Consequently an outer same-interface handler cannot compete with the nearest
one.  Decidable nominal equality selects exactly one of the last two cases.
:::

The “exactly one” statement classifies an operation invocation as a redex when
it has a matching handler and as a request when it does not.  It is not claiming
that a raw operation term is both.

## 5. Configuration decomposition

:::{prf:theorem} Writer configuration decomposition
:label: thm-writer-decomposition-v2

For every closed, well-typed configuration $\langle w,M\rangle$, exactly one
of the following holds:

1. $M=\operatorname{return}V$;
2. there are unique $w',M'$ such that

   $$
   \langle w,M\rangle\longrightarrow\langle w',M'\rangle;
   $$

3. there are unique $\Delta,i,V,E^\Delta$ up to alpha-equivalence such that

   $$
   M=E^\Delta[\operatorname{op}_{\Delta,i}(V)].
   $$
:::

:::{prf:proof}
The unique-active-position lemma gives the syntactic trichotomy.  Ordinary
redexes and handler redexes leave $w$ unchanged and have a unique contractum.
`tell` has the unique transition to $w\cdot a$.  The third case is already the
maximal transparent-context decomposition.  The three cases are disjoint.
:::

## 6. Determinism

:::{prf:corollary} Writer reduction is deterministic
:label: cor-writer-determinism-v2

If

$$
\langle w,M\rangle\longrightarrow\langle w_1,M_1\rangle
$$

and

$$
\langle w,M\rangle\longrightarrow\langle w_2,M_2\rangle,
$$

then $w_1=w_2$ and $M_1=M_2$ up to alpha-equivalence.
:::

:::{prf:proof}
Both transitions must inhabit the unique step case of
{prf:ref}`thm-writer-decomposition-v2` and contract the same active redex.
:::

Multi-shot handlers do not invalidate one-step determinism.  A clause may
explicitly contain two calls to $k$, but evaluating that clause remains an
ordinary deterministic program.  Multi-shot use introduces multiple future
executions, not a choice between reduction rules.

## 7. Substitution lemmas

:::{prf:lemma} Value substitution
:label: lem-writer-value-substitution-v2

If

$$
\Gamma,x:A\vdash M:C!\rho
\qquad\text{and}\qquad
\Gamma\vdash V:A,
$$

then

$$
\Gamma\vdash M[V/x]:C!\rho.
$$
:::

The proof is the usual mutual induction on value and computation typing.
Operation invocations and `tell` use the induction hypothesis on their value
parameter.

:::{prf:lemma} Deep-resumption substitution
:label: lem-writer-resumption-substitution-v2

In an `H-Op-Deep` redex, suppose the operation clause was checked under

$$
k:R_i\to(C!\omega).
$$

Then the inserted value

$$
\lambda y.
\operatorname{handle}_{\Delta}
E^\Delta[\operatorname{return}y]
\operatorname{with}h
$$

has that type, and substituting it for $k$ preserves the clause type
$C!\omega$.
:::

:::{prf:proof}
The typing derivation of the original handled computation gives the residual
typing of the captured evaluation context:

$$
y:R_i\vdash
E^\Delta[\operatorname{return}y]:A!(\rho\cup\{\Delta\}).
$$

Reapply `T-Handle` to obtain

$$
y:R_i\vdash
\operatorname{handle}_{\Delta}
E^\Delta[\operatorname{return}y]\operatorname{with}h:C!\omega.
$$

`T-Abs` gives the required resumption type, and value substitution into the
clause completes the argument.
:::

This proof uses a residual-context typing lemma.  The lemma is syntactic; it
does not yet require a denotational decomposition of the base effect.

## 8. Free-row preservation

:::{prf:theorem} Free-row preservation for Writer
:label: thm-writer-row-preservation-v2

If

$$
\Gamma\vdash M:A!\rho
$$

and

$$
\langle w,M\rangle\longrightarrow\langle w',M'\rangle,
$$

then

$$
\Gamma\vdash M':A!\rho.
$$
:::

:::{prf:proof}
By cases on the contracted redex and reconstruction of its evaluation context.

- Beta, let-return, and Boolean reductions use value substitution.
- `H-Ret` uses substitution into the return clause.
- `H-Op-Deep` uses parameter substitution and
  {prf:ref}`lem-writer-resumption-substitution-v2`.
- `W-Tell` replaces a free-row-silent base primitive by
  $\operatorname{return}()$, which is also free-row silent.
- Context closure follows by the typing rule for the unique surrounding frame.
- Subeffecting restores the displayed upper row where a contractum has a
  smaller principal row.
:::

The theorem preserves only the new free row.  It deliberately says nothing yet
about an exact Writer grade for effectful handler clauses.

## 9. Effect-aware progress and empty-row safety

:::{prf:theorem} Writer effect-aware progress
:label: thm-writer-progress-v2

If

$$
\varnothing\vdash M:A!\rho,
$$

then for every log $w$, exactly one of the following holds:

1. $M=\operatorname{return}V$;
2. $\langle w,M\rangle$ takes a step;
3. $M=E^\Delta[\operatorname{op}_{\Delta,i}(V)]$ for some
   $\Delta\in\rho$.
:::

:::{prf:proof}
The configuration decomposition supplies the three cases.  In the request
case, inversion of `T-Op`, the context typing rules, and subeffecting show that
the exposed interface belongs to the outward row.
:::

:::{prf:corollary} Empty-row unhandled-effect safety
:label: cor-writer-empty-row-v2

A closed computation

$$
\varnothing\vdash M:A!\varnothing
$$

cannot be blocked on an unhandled free operation.
:::

This result permits arbitrary Writer output.  “Empty” refers only to the new
free-effect row.

## 10. Deep elimination

:::{prf:theorem} Dynamic deep elimination
:label: thm-writer-deep-elimination-v2

Suppose

$$
\Gamma\vdash M:A!(\rho\cup\{\Delta\}),
\qquad
\Delta\notin\rho,
$$

and $h$ is exhaustive for $\Delta$ with outward row $\omega$ satisfying

$$
\rho\subseteq\omega,
\qquad
\Delta\notin\omega.
$$

Then

$$
\Gamma\vdash
\operatorname{handle}_{\Delta}M\operatorname{with}h:C!\omega,
$$

and no execution of the handled term can expose an unhandled top-level
$\Delta$ request.
:::

:::{prf:proof}
The typing conclusion is `T-Handle`.  Preservation maintains the outward row
$\omega$ after every step.  If an execution exposed a top-level $\Delta$
request, effect-aware progress inversion would imply $\Delta\in\omega$, in
contradiction with the premise.

Operationally, every matching request originating in the handled computation
is consumed by `H-Op-Deep`; every resumed continuation reinstalls the handler.
The condition $\Delta\notin\omega$ additionally excludes a fresh $\Delta$
request emitted by a clause outside that reinstated continuation.
:::

The theorem is insensitive to whether the input computation actually invokes
$\Delta$.  It is also insensitive to the number of invocations.

## 11. Qualified Writer conservativity

There are two distinct conservativity statements.

:::{prf:theorem} Language-extension conservativity for Writer
:label: thm-writer-language-conservativity-v2

If a source term contains no new free operation and no new handler, its base
typing embeds with empty free row, and its Writer transitions, final value, and
final Writer word are exactly those of the base Writer calculus.
:::

:::{prf:proof}
No new syntactic rule applies.  `T-Base-Projection` assigns the empty free row,
and every transition is an old ordinary or Writer transition.
:::

:::{prf:theorem} Identity-handler inertness on base-only Writer terms
:label: thm-writer-handler-inertness-v2

Let $h$ have the identity return clause

$$
\operatorname{return}(x)\mapsto\operatorname{return}x.
$$

If a closed term $M$ contains no new free operation, then

$$
M
\quad\text{and}\quad
\operatorname{handle}_{\Delta}M\operatorname{with}h
$$

produce the same final value and Writer word whenever either terminates.
:::

:::{prf:proof}
Every ordinary and Writer step of $M$ lifts through the handler context.  Since
no free operation occurs, no operation clause is selected.  At return,
`H-Ret` reduces to the same returned value without emitting Writer output.
:::

Identity return is necessary.  A handler whose return clause performs
`tell(a)` observably changes even a base-only program.  Thus “handlers are inert
on old programs” is not an unconditional conservativity property of arbitrary
handler terms.

## 12. Assumptions actually used

The Writer proofs used the following base facts.

| Result | Base-specific facts used |
|---|---|
| decomposition | `tell` is either a unique primitive redex or absent |
| determinism | deterministic Writer transition and unique CBV context |
| row preservation | `tell` and its result are free-row silent |
| empty-row safety | every closed `tell` invocation can step |
| deep elimination | none beyond row preservation and progress |
| language conservativity | new rules do not rewrite old syntax |
| handler inertness | base steps lift through handler contexts; identity return |

Notably absent are commutativity, idempotence, cancellation, and a Writer
iteration operator.  Those structures become relevant only when asking for a
precise static Writer grade after effectful handling.

## 13. Remaining gaps

The following are not proved on this page.

- strong normalization or termination of unrestricted multi-shot programs;
- a denotational interpretation of handler clauses;
- adequacy with respect to a Writer-plus-free interaction tree;
- a principal Writer-grade transformer for effectful handlers;
- contextual equivalence or logical relations.

The next development should define the concrete tree semantics and prove that
one operational reduction preserves its denotation.  Adequacy can then be
proved by the same return/request decomposition used above.
