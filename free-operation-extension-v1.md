# Free-operation extension v1

## Status

**Current Stage 1 candidate: exact free-operation skeleton, no handlers.**

This page extends the fixed Stage 0 calculus with free operations only. It investigates whether syntax, operational decomposition, graded denotation, and Writer adequacy extend naturally.

No handler syntax or reduction rule is present.

## 1. Design decision

Base effects remain upper approximations inside each base segment. Free-operation tokens are initially exact:

> If the effect index contains a free token $\Delta$, every execution path represented by that typing derivation exposes exactly one operation from $\Delta$ at that position.

Consequently, Stage 1 does **not** add a coercion that inserts or deletes a $\Delta$ token.

This decision is deliberately restrictive. It gives a clean conservative extension and lets us identify precisely when an optional/skip layer becomes necessary.

## 2. Free interfaces and syntax

Let $\mathcal D$ be a collection of interfaces. Each $\Delta\in\mathcal D$ contains operation symbols

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}.
$$

Extend computations by

$$
M::=\cdots\mid\operatorname{op}_\Delta(V).
$$

The operation is a simple computation. It does not take a continuation argument.

For example,

$$
\mathsf{choose}_\Delta(*):\mathsf{Bool}.
$$

Subsequent computation uses ordinary `let`:

```text
let x <- choose_Delta(*) in M
```

## 3. Extended effects

Let $\mathcal D^*$ be the free monoid on free-interface tokens and define

$$
\widehat B=B*\mathcal D^*.
$$

The product is sequential concatenation followed only by:

- multiplication of adjacent $B$ factors;
- concatenation of adjacent free-token blocks;
- deletion of monoid units.

There is no commutation equation between $b\in B$ and $\Delta\in\mathcal D$.

Thus generally

$$
b\cdot\Delta\neq\Delta\cdot b.
$$

### Extended preorder

The preorder is generated componentwise from the base preorder while preserving the exact free skeleton. Schematically,

$$
b_0\Delta_1b_1\cdots\Delta_nb_n
\leq
b'_0\Delta_1b'_1\cdots\Delta_nb'_n
$$

when $b_i\leq b'_i$ for every $i$.

Words with different free-token sequences are incomparable. In particular,

$$
1\not\leq\Delta.
$$

## 4. Typing extension

Embed each base grade $b$ into $\widehat B$. All Stage 0 typing rules are retained under this embedding.

Add only:

$$
\frac{
\operatorname{op}:P\to R\in\Delta
\qquad
\Gamma\vdash V:P}
{
\Gamma\vdash\operatorname{op}_\Delta(V):R!\Delta}.
\tag{T-Free-Op}
$$

`T-Let` now multiplies extended words:

$$
\frac{
\Gamma\vdash M:A!E
\qquad
\Gamma,x:A\vdash N:C!F}
{
\Gamma\vdash
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
:C!(E\cdot F)}.
$$

No other rule changes.

### Conservative extension

If a term contains no free operation, its typing derivation uses only embedded base grades and is exactly a Stage 0 derivation. No new subeffecting relation exists between distinct base-only grades.

## 5. Operational semantics

There is no internal reduction rule for $\operatorname{op}_\Delta(V)$. Evaluation contexts remain

$$
\mathcal E::=[-]
\mid
\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N.
$$

A free request is an observable form

$$
\mathcal E[\operatorname{op}_\Delta(V)].
$$

An external responder may supply $W:R_{\operatorname{op}}$ by

$$
\mathcal E[\operatorname{op}_\Delta(V)]
\xRightarrow{\operatorname{op}(V)\mapsto W}
\mathcal E[\mathsf{return}\;W].
$$

This is not a handler. It is a labelled environment response used to expose the residual computation. Stage 2 will define which contexts a shallow handler captures and how its clauses respond.

## 6. Extended decomposition

### Theorem F-001

Every closed well-typed Stage 1 computation is uniquely one of:

1. $\mathsf{return}\;V$;
2. $\mathcal E[\beta(V)]$ for a base request;
3. $\mathcal E[\operatorname{op}_\Delta(V)]$ for a free request;
4. able to take one unique internal step.

### Proof

The Stage 0 decomposition induction gains one syntax case. A free-operation term is case 3; a `let` whose left side is case 3 extends the unique evaluation context. No reduction rule overlaps with a free request. $\square$

Hence substitution, internal preservation, and internal determinism are conservative extensions of the Stage 0 proofs.

## 7. One-operation shape functor

Define

$$
\mathsf{Op}_\Delta Z
=
\coprod_{\operatorname{op}:P\to R\in\Delta}
P\times Z^R.
$$

An element records:

- the selected operation;
- its parameter;
- for every possible result, the residual computation.

The continuation occurs in the **denotation of the surrounding `let` context**, even though it is not a syntactic argument of `op`.

## 8. Exact-layer graded carrier

Write an extended word in fine alternating notation

$$
E=b_0\Delta_1b_1\cdots\Delta_nb_n,
$$

allowing identity base segments where convenient. Define recursively:

$$
\widehat T_bX=T_bX,
$$

$$
\widehat T_{b\Delta E}X
=
T_b\bigl(
\mathsf{Op}_\Delta(\widehat T_EX)
\bigr).
$$

For a pure free token this gives

$$
\widehat T_\Delta X
=
T_1\bigl(
\mathsf{Op}_\Delta(T_1X)
\bigr).
$$

The outer and inner $T_1$ retain the possibly non-strict pure component of the base graded monad. If $T_1=\mathsf{Id}$ strictly, this simplifies to $\mathsf{Op}_\Delta X$.

### No return/skip branch

There is intentionally no coproduct

$$
X+\mathsf{Op}_\Delta(K)
$$

or

$$
K+\mathsf{Op}_\Delta(K).
$$

At exact grade $\Delta$, a free operation must be exposed. A computation that simply returns has grade $1$, not $\Delta$.

Thus the earlier return-vs-tail problem is postponed rather than solved by fiat. It reappears exactly when the type system gains an optional-layer coercion such as $1\leq\Delta$ or an explicit `pad_Delta` constructor.

## 9. Primitive free-operation denotation

For $\operatorname{op}:P\to R\in\Delta$, first construct

$$
P
\to
\mathsf{Op}_\Delta(T_1R)
$$

by selecting the $\operatorname{op}$ summand and mapping

$$
p
\mapsto
(p,\lambda r.\eta(r)).
$$

Then apply the outer base unit:

$$
\operatorname{op}^{\widehat T}:
P
\to
T_1(\mathsf{Op}_\Delta(T_1R))
=
\widehat T_\Delta R.
$$

Hence

$$
\llbracket\operatorname{op}_\Delta(V)\rrbracket
=
\operatorname{op}^{\widehat T}
\circ\llbracket V\rrbracket.
$$

No source-level continuation was introduced.

## 10. Extended bind

The graded bind

$$
\widehat T_EX
\times
(X\to\widehat T_FY)
\longrightarrow
\widehat T_{E\cdot F}Y
$$

is defined by induction on the free-token structure of $E$.

### Base-only case

If $E=b$ and $F$ begins with base segment $c$, write

$$
\widehat T_FY=T_cZ.
$$

Use the base graded bind

$$
T_bX
\times(X\to T_cZ)
\to T_{b\cdot c}Z.
$$

This merges the adjacent base segments at the concatenation boundary.

### Free-layer case

For

$$
m\in
T_b(\mathsf{Op}_\Delta(\widehat T_EX)),
$$

recursively bind $f$ into every residual leaf

$$
\widehat T_EX\to\widehat T_{E\cdot F}Y,
$$

map that function through $\mathsf{Op}_\Delta$, and then through $T_b$.

The existing free node and all preceding base segments remain unchanged. Only its residual computation is extended.

### Laws

Unit and associativity follow by induction on $E$:

- base cases are the base graded-monad laws;
- free cases reduce to functoriality of $T_b$ and $\mathsf{Op}_\Delta$ plus the induction hypothesis.

Subeffect coercions map componentwise through the same nested functors. Coherence reduces to Stage 0 coercion coherence.

Therefore the exact-layer construction is a candidate $\widehat B$-graded monad and restricts to $T$ on base-only grades.

## 11. Two programs that show order

Let $\mathsf{choose}:1\to\mathsf{Bool}\in\Delta$.

### Free operation before Writer

```text
let x <- choose_Delta(*) in
if x then
  let u <- tell("T") in return x
else
  let u <- tell("F") in return x
```

Its grade is

$$
\Delta\cdot w.
$$

In the strict Writer instance $T_1=\mathsf{Id}$, its denotation is a `choose` node whose residual map is

$$
\mathsf{true}\mapsto([\text{"T"}],\mathsf{true}),
$$

$$
\mathsf{false}\mapsto([\text{"F"}],\mathsf{false}).
$$

Operationally the first observation is `choose`; no Writer log exists until the environment supplies a Boolean.

### Writer before free operation

```text
let u <- tell("before") in
let x <- choose_Delta(*) in
return x
```

Its grade is

$$
w\cdot\Delta.
$$

The Writer machine first records `"before"` and only then exposes `choose`. Its denotation lies in

$$
T_w(\mathsf{Op}_\Delta(T_1\mathsf{Bool}))
$$

and contains the prefix log outside the free node.

Thus $w\Delta$ and $\Delta w$ are operationally and denotationally distinct.

## 12. Writer tree semantics

To compare unhandled free operations with execution, replace a single final Writer result by a finite interaction tree indexed by the exact word.

Define

$$
\mathsf{WTree}_bX
=
T_bX,
$$

$$
\mathsf{WTree}_{b\Delta E}X
=
T_b\bigl(
\mathsf{Op}_\Delta(\mathsf{WTree}_EX)
\bigr).
$$

For Writer, this is exactly the carrier $\widehat T_EX$.

Operationally, construct the tree by:

1. running internal and Writer steps until return or a free request is exposed;
2. at $\mathcal E[\operatorname{op}_\Delta(V)]$, recording the operation and parameter;
3. for every possible result $r$, recursively exploring

   $$
   \mathcal E[\mathsf{return}\;r].
   $$

Because the calculus has no recursion and the effect word contains finitely many exact free tokens, every branch of this construction terminates.

## 13. Tree adequacy

### Theorem F-002 — Writer/free-tree adequacy

For a closed Stage 1 term

$$
\vdash M:A!E,
$$

the operational Writer/free interaction tree is equal to

$$
\llbracket M\rrbracket
\in\widehat T_E\llbracket A\rrbracket,
$$

after interpreting returned closed ground values in $\mathbf{Set}$.

### Proof sketch

Induction on the free-token length of $E$.

- If the length is zero, this is Writer evaluation soundness/adequacy from Stage 0.
- For $E=b\Delta F$, run the leading Writer/base segment. F-001 and exact typing ensure that the next non-base boundary is a matching operation from $\Delta$, not a return and not a different free skeleton. The operation tag and parameter agree with the selected polynomial summand. For each result $r$, the residual term has grade $F$; apply the induction hypothesis pointwise to its continuation.

The `let` case agrees because operational tree substitution and $\widehat T$-bind are defined by the same recursion, while Writer segments compose by log concatenation. $\square$

This is a paper-level theorem conditional on the exact-effect inversion lemma stated below.

### Required inversion lemma

If a closed term has grade $b\Delta E$, then after the leading base machine segment it cannot return before exposing a $\Delta$ request. This follows only because the extended preorder does not insert/delete free tokens. A fully formal proof proceeds by typing inversion plus preservation for labelled base-machine steps.

## 14. Which Writer properties are preserved?

| Property | Stage 1 status | Change |
|---|---|---|
| WP-1 deterministic decomposition | Preserved | adds a unique free-request case |
| WP-2 termination | Reformulated | terminates to a free boundary; with responses, every branch terminates |
| WP-3 one-step invariant | Preserved relationally | free request corresponds to a polynomial node |
| WP-4 evaluation soundness | Generalized | evaluation produces an interaction tree |
| WP-5 ground adequacy | Generalized | Bool/log adequacy becomes tree adequacy F-002 |
| WP-6 pure-effect reflection | Preserved | each base segment graded $1$ has empty log |
| WP-7 ordered sequencing | Preserved | $\widehat T$-bind substitutes trees and concatenates base segments |
| WP-8 contextual soundness | Preserved conditionally | compositional tree equality implies equal observations under any later sound interpreter |

Thus the natural exact extension preserves the structural package, but changes the observation object from a final `(log,value)` pair to a free interaction tree.

## 15. What is not preserved automatically

### Total evaluation to a value

An unhandled free request intentionally stops evaluation. WP-2 cannot remain “every closed term returns a value” without supplying a responder.

### Optional free operations

The program

```text
if c then
  choose_Delta(*)
else
  return false
```

does not type at one exact free skeleton: the branches have grades $\Delta$ and $1$.

To admit it, Stage 1 would need one of:

1. a coercion/padding rule $1\leq\Delta$;
2. an explicit boundary constructor such as `pad_Delta M`;
3. a separate upper-bound free-effect system;
4. a sum carrier with a skip branch.

Only at that point must we choose between value-return and tail-computation branches and revisit handler return behavior.

### Arbitrary base graded monads

The recursive carrier requires $T_b$ and each polynomial $\mathsf{Op}_\Delta$ to act functorially, and extended open-term semantics requires strengths/coherence through the nested construction. These are genuine hypotheses.

## 16. Stage 1 conclusion

Under exact free skeletons, there is a natural conservative extension:

$$
T_bX
\quad\leadsto\quad
\widehat T_{b\Delta E}X
=
T_b(\mathsf{Op}_\Delta(\widehat T_EX)).
$$

It preserves substitution, internal type safety, deterministic decomposition, graded sequencing, base conservativity, and a generalized tree adequacy property.

The price is intentional:

- free requests become observable boundaries until an interpreter/handler is supplied;
- optional occurrence of a free operation is not expressible at one exact grade;
- Stage 2 must define matching shallow handlers as interpreters of exposed polynomial nodes, while preserving the tree relation.

This exact construction is therefore the clean baseline against which any optional-layer extension should be compared.

