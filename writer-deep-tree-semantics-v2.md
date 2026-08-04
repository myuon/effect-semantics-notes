# Writer deep-tree semantics v2

## Status

**Concrete denotational construction and paper proofs.** Reduction soundness
and handler commutation are unconditional for the recursion-free syntax.
The stated operational adequacy theorem is conditional on termination of the
closed computation; a separate normalization proof for unrestricted
multi-shot clauses remains open.

## 1. Why normalize Writer nodes

A raw interaction tree could use

$$
\mathsf{ret}(a),
\qquad
\mathsf{tell}(w,t),
\qquad
\mathsf{req}_{\Delta,i}(p,k).
$$

Operational configurations, however, accumulate Writer output immediately:

$$
\langle u,\operatorname{tell}(w)\rangle
\longrightarrow
\langle u\cdot w,\operatorname{return}()\rangle.
$$

Then raw trees would identify operationally equivalent shapes such as

$$
\mathsf{tell}(u,\mathsf{tell}(w,t))
$$

and

$$
\mathsf{tell}(u\cdot w,t)
$$

only after quotienting.  We avoid that quotient by storing one Writer segment
before every return or free request.

## 2. Writer-normalized interaction trees

For a set $A$, define well-founded trees by

$$
\mathsf{WTree}_{\Sigma}A
\cong
W\times\left(
A+
\sum_{\Delta\in\mathcal D}
\sum_{i\in I_\Delta}
P_i\times(R_i\to\mathsf{WTree}_{\Sigma}A)
\right).
$$

We write their constructors as

$$
\mathsf{ret}_W(w,a)
$$

and

$$
\mathsf{req}_W(w;\Delta,i,p,k).
$$

The segment $w$ is the Writer output produced since the previous free request,
or since execution began.

For finite row $\rho$, define

$$
\mathsf{WTree}_\rho A
$$

as the trees whose every request interface belongs to $\rho$.

## 3. Prefixing Writer output

Define

$$
\mathsf{prefix}_u:\mathsf{WTree}_\rho A\to\mathsf{WTree}_\rho A
$$

by multiplying only the first segment:

$$
\mathsf{prefix}_u(\mathsf{ret}_W(w,a))
=
\mathsf{ret}_W(u\cdot w,a),
$$

$$
\mathsf{prefix}_u(\mathsf{req}_W(w;\Delta,i,p,k))
=
\mathsf{req}_W(u\cdot w;\Delta,i,p,k).
$$

Then

$$
\mathsf{prefix}_\epsilon=\mathrm{id},
$$

$$
\mathsf{prefix}_u\circ\mathsf{prefix}_w
=
\mathsf{prefix}_{u\cdot w}.
$$

These equations use exactly the Writer monoid laws.

## 4. Monad structure

The unit is

$$
\eta(a)=\mathsf{ret}_W(\epsilon,a).
$$

Bind is defined structurally:

$$
\mathsf{ret}_W(w,a)\mathbin{\gg=}f
=
\mathsf{prefix}_w(f(a)),
$$

$$
\mathsf{req}_W(w;\Delta,i,p,k)\mathbin{\gg=}f
=
\mathsf{req}_W
(w;\Delta,i,p,\lambda r.k(r)\mathbin{\gg=}f).
$$

:::{prf:lemma} Writer-tree prefix/bind compatibility
:label: lem-wtree-prefix-bind-v2

$$
\mathsf{prefix}_u(t)\mathbin{\gg=}f
=
\mathsf{prefix}_u(t\mathbin{\gg=}f).
$$
:::

:::{prf:proof}
By cases on $t$.  The return case is associativity in $W$; the request case is
definitionally equal because prefix changes only the root segment.
:::

:::{prf:theorem} Writer-normalized trees form a monad
:label: thm-wtree-monad-v2

$\mathsf{WTree}_\Sigma$ with $\eta$ and bind above satisfies left unit, right
unit, and associativity.  Row-refined carriers satisfy

$$
\mathsf{WTree}_\rho A
\times
(A\to\mathsf{WTree}_\sigma C)
\longrightarrow
\mathsf{WTree}_{\rho\cup\sigma}C.
$$
:::

:::{prf:proof}
Structural induction on the first tree.  Left unit unfolds to
$\mathsf{prefix}_\epsilon$.  Right unit uses the fact that prefixing a pure
return appends its empty segment.  Associativity uses
{prf:ref}`lem-wtree-prefix-bind-v2` in the return case and the induction
hypothesis pointwise in request continuations.  Row closure follows because
bind preserves old request nodes and introduces only nodes from the result of
$f$.
:::

## 5. Interpretation of syntax

Values are interpreted as usual.  Computations are interpreted by:

$$
\llbracket\operatorname{return}V\rrbracket
=
\mathsf{ret}_W(\epsilon,\llbracket V\rrbracket),
$$

$$
\llbracket
\mathbf{let}\ x\leftarrow M\ \mathbf{in}\ N
\rrbracket
=
\llbracket M\rrbracket\mathbin{\gg=}
(\lambda x.\llbracket N\rrbracket),
$$

$$
\llbracket\operatorname{tell}(w)\rrbracket
=
\mathsf{ret}_W(w,()),
$$

$$
\llbracket\operatorname{op}_{\Delta,i}(V)\rrbracket
=
\mathsf{req}_W
(\epsilon;\Delta,i,\llbracket V\rrbracket,
\lambda r.\mathsf{ret}_W(\epsilon,r)).
$$

Application, conditionals, and substitution use the standard fine-grain CBV
interpretation.

:::{prf:lemma} Row soundness of the tree interpretation
:label: lem-wtree-row-sound-v2

If

$$
\Gamma\vdash M:A!\rho,
$$

then

$$
\llbracket M\rrbracket
\in
\mathsf{WTree}_\rho\llbracket A\rrbracket.
$$
:::

:::{prf:proof}
By induction on typing.  `T-Op` introduces one request from its singleton row,
`T-Base-Projection` interprets `tell` without a free node, sequencing uses the
row-refined bind, and subsumption uses row inclusion.  The handler case follows
from the deep-handler theorem below.
:::

## 6. Deep handlers as folds

Fix a handler from result type $A$ to $C$.  Its denotational clauses are:

$$
r:A\to\mathsf{WTree}_\omega C
$$

and, for each $\operatorname{op}_i:P_i\to R_i$ in $\Delta$,

$$
c_i:
P_i\to
(R_i\to\mathsf{WTree}_\omega C)
\to
\mathsf{WTree}_\omega C.
$$

Define

$$
H_{\Delta,h}:\mathsf{WTree}_{\rho\cup\{\Delta\}}A
\to\mathsf{WTree}_\omega C
$$

by

$$
H_{\Delta,h}(\mathsf{ret}_W(w,a))
=
\mathsf{prefix}_w(r(a)),
\tag{DH-Ret}
$$

$$
\begin{aligned}
&H_{\Delta,h}
(\mathsf{req}_W(w;\Delta,i,p,k))\\
&\quad=
\mathsf{prefix}_w
\left(c_i(p,\lambda x.H_{\Delta,h}(k(x)))\right),
\end{aligned}
\tag{DH-Match}
$$

and, for $\Gamma\neq\Delta$,

$$
\begin{aligned}
&H_{\Delta,h}
(\mathsf{req}_W(w;\Gamma,j,p,k))\\
&\quad=
\mathsf{req}_W
(w;\Gamma,j,p,\lambda x.H_{\Delta,h}(k(x))).
\end{aligned}
\tag{DH-Forward}
$$

`DH-Forward` recursively retains the pending handler.  `DH-Match` passes a
recursively handled resumption to the clause.  The whole clause result is not
wrapped again, so a fresh $\Delta$ emitted directly by the clause escapes unless
another handler catches it.  This matches the direct operational scope.

:::{prf:theorem} Denotational deep elimination
:label: thm-wtree-deep-elimination-v2

If $\Delta\notin\rho$, every return and operation clause lies in
$\mathsf{WTree}_\omega C$, and $\Delta\notin\omega$, then

$$
H_{\Delta,h}:
\mathsf{WTree}_{\rho\cup\{\Delta\}}A
\to
\mathsf{WTree}_\omega C
$$

contains no $\Delta$ request in its result.
:::

:::{prf:proof}
Structural induction.  Matching nodes are replaced by clause trees;
nonmatching nodes retain only their distinct interface and recursively handled
continuations; clause trees are $\Delta$-free by $\Delta\notin\omega$.
:::

## 7. Handler substitution equation

Let $E^\Delta$ be a captured transparent context and define

$$
K(x)=
\llbracket E^\Delta[\operatorname{return}x]\rrbracket.
$$

The direct matching reduction substitutes

$$
\lambda x.
\operatorname{handle}_\Delta
E^\Delta[\operatorname{return}x]
\operatorname{with}h.
$$

Denotationally this value is exactly

$$
\lambda x.H_{\Delta,h}(K(x)).
$$

Consequently `H-Op-Deep` and `DH-Match` use the same resumption.

This equality is the central reason the standard deep semantics is simpler
than the previous first-free-head shallow transformer: matching and forwarding
are both structural recursion, while the distinction is localized to whether
the clause result itself is rehandled.

## 8. Configuration denotation

For a configuration with accumulated Writer log $u$, define

$$
\llbracket\langle u,M\rangle\rrbracket_{\mathrm{cfg}}
=
\mathsf{prefix}_u(\llbracket M\rrbracket).
$$

This makes the Writer transition an equality:

$$
\begin{aligned}
\llbracket\langle u,\operatorname{tell}(w)\rangle\rrbracket_{\mathrm{cfg}}
&=
\mathsf{ret}_W(u\cdot w,()),\\
\llbracket\langle u\cdot w,\operatorname{return}()\rangle\rrbracket_{\mathrm{cfg}}
&=
\mathsf{ret}_W(u\cdot w,()).
\end{aligned}
$$

## 9. One-step soundness

:::{prf:theorem} Writer one-step denotational soundness
:label: thm-wtree-step-sound-v2

If

$$
\langle u,M\rangle\longrightarrow\langle u',M'\rangle,
$$

then

$$
\llbracket\langle u,M\rangle\rrbracket_{\mathrm{cfg}}
=
\llbracket\langle u',M'\rangle\rrbracket_{\mathrm{cfg}}.
$$
:::

:::{prf:proof}
By cases on the contracted redex.

- Beta, let-return, and conditionals use the semantic substitution lemma and
  monad unit laws.
- `W-Tell` is the calculation above.
- `H-Ret` is `DH-Ret` plus substitution into the return clause.
- `H-Op-Deep` is `DH-Match` plus the handler substitution equation.
- Context closure uses compositionality; a Writer-changing inner step uses
  {prf:ref}`lem-wtree-prefix-bind-v2`.
:::

## 10. Return and request reflection

:::{prf:lemma} Return reflection
:label: lem-wtree-return-reflection-v2

If a closed configuration evaluates to

$$
\langle w,\operatorname{return}V\rangle,
$$

then its configuration denotation is

$$
\mathsf{ret}_W(w,\llbracket V\rrbracket).
$$
:::

This follows immediately by iterating one-step soundness.

:::{prf:lemma} Request reflection
:label: lem-wtree-request-reflection-v2

If evaluation exposes

$$
E^\Delta[\operatorname{op}_{\Delta,i}(V)]
$$

with accumulated log $w$, then the configuration denotation has outer shape

$$
\mathsf{req}_W
(w';\Delta,i,\llbracket V\rrbracket,k)
$$

for the Writer segment $w'$ accumulated before the request, and $k$ is the
denotation of its request continuation.
:::

:::{prf:proof}
Induction on the transparent context.  A let frame becomes tree bind.  A
nonmatching handler frame becomes `DH-Forward`, which preserves the request
label and recursively transforms its continuation.  Writer steps before the
request are accumulated into the root segment.
:::

## 11. Termination-conditional adequacy

:::{prf:theorem} Writer tree adequacy, conditional form
:label: thm-wtree-adequacy-v2

Let $M$ be closed and well typed at a first-order observable result type.
Assume its deterministic evaluation reaches either a return or an unhandled
request.  Then:

1. it returns some value $V$ with log $w$ and semantic value
   $a=\llbracket V\rrbracket$ iff its configuration denotation is

   $$
   \mathsf{ret}_W(w,a);
   $$

2. it exposes interface $\Delta$ and operation $i$ after segment $w$ iff its
   denotation has corresponding outer request shape

   $$
   \mathsf{req}_W(w;\Delta,i,p,k).
   $$
:::

:::{prf:proof}
The forward directions are return and request reflection.  For the reverse
directions, repeatedly use deterministic configuration decomposition.  A step
preserves denotation.  A return and a request have disjoint tree constructors,
so evaluation cannot terminate in the wrong form.  Under the stated
termination assumption it must reach the form named by the denotation.
:::

The remaining normalization question is deliberately separated.  In the
recursion-free linear fragment it should follow by the usual reducibility
argument.  For unrestricted multi-shot clauses we still need a measure or
reducibility proof showing that finite duplication of captured residual
computations preserves normalization in this exact calculus.

## 12. Operational/denotational handler commutation

:::{prf:theorem} Deep handler commutation
:label: thm-wtree-handler-commutation-v2

For every handled term,

$$
\llbracket
\operatorname{handle}_\Delta M\operatorname{with}h
\rrbracket
=
H_{\Delta,\llbracket h\rrbracket}(\llbracket M\rrbracket).
$$

Moreover, the operational matching, forwarding, and return rules correspond
respectively to `DH-Match`, `DH-Forward`, and `DH-Ret`.
:::

The first equation is the definition of the handler interpretation.  Its
content is validated by one-step soundness and the three constructor cases.

## 13. The six examples denotationally

The examples from [Writer deep-handler examples
v2](writer-deep-handler-examples-v2.md) yield:

1. conditional false:
   $\mathsf{ret}_W(\epsilon,\mathsf{false})$;
2. forwarded Ping then Ask under both handlers:
   $\mathsf{ret}_W(\epsilon,\mathsf{true})$;
3. two deep Ask requests with the true handler:
   $\mathsf{ret}_W(\epsilon,\mathsf{true})$;
4. zero, one, and two Ask requests under a logging clause:
   root Writer segments $\epsilon$, $a$, and $aa$;
5. linear logging handlers around Ping then Ask:
   $\mathsf{ret}_W(pa,())$;
6. a base-only `tell(w)` under identity-return handling:
   $\mathsf{ret}_W(w,())$.

These are direct calculations from `DH-Ret`, `DH-Match`, and `DH-Forward`.

## 14. Exact-grade obstruction

:::{prf:theorem} No exact Writer output from row data alone
:label: thm-row-only-writer-obstruction-v2

Let $W$ be the free monoid on letter $a$.  There is no function

$$
F:W\times\mathcal P_{\mathrm{fin}}(\mathcal D)\times W\to W
$$

that, from only

1. the exact base Writer output before handling,
2. the input unordered free row, and
3. the exact Writer output of one handler-clause invocation,

returns the exact handled Writer output for every well-typed program.
:::

:::{prf:proof}
Take three programs with no Writer output before handling and the common row
upper bound $\{\mathsf{Ask}\}$:

$$
M_0=\operatorname{return}(),
$$

$$
M_1=\operatorname{ask}();\operatorname{return}(),
$$

$$
M_2=\operatorname{ask}();\operatorname{ask}();\operatorname{return}().
$$

Handle each with the deep clause that emits $a$ once and resumes.  Their exact
outputs are respectively

$$
\epsilon,
\qquad
a,
\qquad
aa.
$$

All three inputs supplied to $F$ are $(\epsilon,\{\mathsf{Ask}\},a)$, so $F$
would have to return three distinct free-monoid elements on the same argument.
:::

This theorem rules out an **exact** transformer.  It does not rule out a safe
upper approximation such as a top element, a closure $a^*$, an occurrence
bound, or a trace-language refinement.

## 15. Base laws used by the denotational proof

The construction used:

- a Writer monoid for segment concatenation;
- algebraicity of `tell`, realized by prefix/bind compatibility;
- a free request signature exposing response-indexed continuations;
- exhaustive nominal matching;
- structural recursion on well-founded trees;
- deep reinstallation in matching and nonmatching continuations.

It did not use commutativity or idempotence.  Compared with the operational
proof, the new substantive structure is the free tree presentation.  The
ordinary Writer monad $A\times W$ alone does not expose free request nodes.

## 16. Next step

Before abstracting these proofs, repeat the same six programs and property
audit for State.  State will test whether the Writer proof's use of a simple
prefix action generalizes when a base operation returns information that
changes the continuation.
