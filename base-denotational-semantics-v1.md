# Base denotational semantics v1

## Status

**Current Stage 0 denotational candidate.**

This page interprets only [Base calculus v1](base-calculus-v1.md). It does not yet interpret free operations, handlers, or recursion.

## 1. Semantic assumptions

Let $\mathcal C$ be a bicartesian closed category. Thus it has:

- a terminal object $1$;
- finite products $A\times B$;
- finite coproducts $A+B$;
- exponentials $B^A$.

At Stage 0 this causes no fixpoint collapse, because we do **not** equip every object and morphism of $\mathcal C$ with fixed points. The later recursion constraint is recorded in [Fixpoint design constraints](fixpoint-design.md).

Let

$$
(B,\cdot,1_B,\leq)
$$

be the base-effect preordered monoid.

## 2. Strong graded monad

For every $b\in B$, assume an endofunctor

$$
T_b:\mathcal C\to\mathcal C.
$$

The graded unit and multiplication are

$$
\eta_A:A\to T_{1_B}A,
$$

$$
\mu_{b,c,A}:T_bT_cA\to T_{b\cdot c}A.
$$

They satisfy the graded left/right unit and associativity laws.

For subeffecting $b\leq c$, assume a natural coercion

$$
\tau_{b,c,A}:T_bA\to T_cA
$$

such that

$$
\tau_{b,b}=\mathsf{id},
\qquad
\tau_{c,d}\circ\tau_{b,c}=\tau_{b,d},
$$

and $\tau$ commutes with $\eta$ and $\mu$.

To interpret open call-by-value sequencing, each $T_b$ has tensorial strength

$$
\mathsf{st}_{b,X,A}:
X\times T_bA\to T_b(X\times A),
$$

natural in $X,A$ and coherent with products, $\eta$, $\mu$, and $\tau$.

Equivalently, $b\mapsto T_b$ is a suitably strong lax monoidal interpretation of the effect monoid in endofunctors of $\mathcal C$.

## 3. Base operations

Every primitive base operation

$$
\beta:P_\beta\to R_\beta,
\qquad |\beta|\in B
$$

is interpreted by a morphism

$$
\beta^T:
\llbracket P_\beta\rrbracket
\to
T_{|\beta|}\llbracket R_\beta\rrbracket.
$$

This matches the source typing

$$
\beta(V):R_\beta!|\beta|.
$$

No continuation is supplied to $\beta^T$. Sequencing with the rest of the program is interpreted separately by graded bind.

## 4. Types and contexts

Primitive types $\iota$ are assigned chosen objects $\llbracket\iota\rrbracket$ of $\mathcal C$. The remaining types are interpreted by

$$
\llbracket1\rrbracket=1,
$$

$$
\llbracket\mathsf{Bool}\rrbracket=1+1,
$$

$$
\llbracket A\times B\rrbracket
=\llbracket A\rrbracket\times\llbracket B\rrbracket,
$$

$$
\llbracket A+B\rrbracket
=\llbracket A\rrbracket+\llbracket B\rrbracket,
$$

$$
\llbracket A\to(B!b)\rrbracket
=
\bigl(T_b\llbracket B\rrbracket\bigr)^{\llbracket A\rrbracket}.
$$

Contexts are interpreted by finite products:

$$
\llbracket x_1:A_1,\ldots,x_n:A_n\rrbracket
=
\prod_i\llbracket A_i\rrbracket.
$$

## 5. Judgments

A value derivation denotes

$$
\llbracket\Gamma\vdash V:A\rrbracket:
\llbracket\Gamma\rrbracket\to\llbracket A\rrbracket.
$$

A computation derivation denotes

$$
\llbracket\Gamma\vdash M:A!b\rrbracket:
\llbracket\Gamma\rrbracket\to T_b\llbracket A\rrbracket.
$$

The denotation is initially defined on typing derivations. Coherence for different placements of `T-Sub` is a separate theorem.

## 6. Value clauses

Variables denote projections; unit, booleans, pairs, and injections use the corresponding categorical structure.

If

$$
m=
\llbracket\Gamma,x:A\vdash M:B!b\rrbracket:
\llbracket\Gamma\rrbracket\times\llbracket A\rrbracket
\to T_b\llbracket B\rrbracket,
$$

then abstraction is currying:

$$
\llbracket\lambda x.M\rrbracket
=\Lambda(m):
\llbracket\Gamma\rrbracket
\to
\bigl(T_b\llbracket B\rrbracket\bigr)^{\llbracket A\rrbracket}.
$$

## 7. Computation clauses

Write $\gamma=\llbracket\Gamma\rrbracket$.

### Return

For $v:\gamma\to\llbracket A\rrbracket$,

$$
\llbracket\mathsf{return}\;V\rrbracket
=
\eta_{\llbracket A\rrbracket}\circ v:
\gamma\to T_{1_B}\llbracket A\rrbracket.
$$

### Application

For

$$
v:\gamma\to
(T_b\llbracket B\rrbracket)^{\llbracket A\rrbracket}
$$

and $w:\gamma\to\llbracket A\rrbracket$,

$$
\llbracket V\,W\rrbracket
=
\mathsf{ev}\circ\langle v,w\rangle:
\gamma\to T_b\llbracket B\rrbracket.
$$

### Sequencing

Suppose

$$
m:\gamma\to T_b\llbracket A\rrbracket
$$

and

$$
n:\gamma\times\llbracket A\rrbracket
\to T_c\llbracket C\rrbracket.
$$

Then

$$
\llbracket
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
\rrbracket
$$

is the composite

$$
\begin{aligned}
\gamma
&\xrightarrow{\langle\mathsf{id},m\rangle}
\gamma\times T_b\llbracket A\rrbracket\\
&\xrightarrow{\mathsf{st}_b}
T_b(\gamma\times\llbracket A\rrbracket)\\
&\xrightarrow{T_b n}
T_bT_c\llbracket C\rrbracket\\
&\xrightarrow{\mu_{b,c}}
T_{b\cdot c}\llbracket C\rrbracket.
\end{aligned}
$$

This is graded call-by-value bind. It is the semantic counterpart of source-level `let`, not a continuation argument to an operation.

### Base operation

For $v:\gamma\to\llbracket P_\beta\rrbracket$,

$$
\llbracket\beta(V)\rrbracket
=
\beta^T\circ v:
\gamma\to T_{|\beta|}\llbracket R_\beta\rrbracket.
$$

### Subeffecting

If $b\leq c$ and $m:\gamma\to T_b\llbracket A\rrbracket$, then

$$
\llbracket\mathsf{T\text{-}Sub}(m)\rrbracket
=
\tau_{b,c}\circ m.
$$

### Conditionals

Let

$$
v:\gamma\to1+1
$$

and $m,n:\gamma\to T_b\llbracket A\rrbracket$. Using distributivity

$$
\gamma\times(1+1)\cong\gamma+\gamma,
$$

the conditional denotes

$$
\gamma
\xrightarrow{\langle\mathsf{id},v\rangle}
\gamma\times(1+1)
\xrightarrow{\cong}
\gamma+\gamma
\xrightarrow{[m,n]}
T_b\llbracket A\rrbracket.
$$

The order of $m,n$ is chosen consistently with the injections representing `true` and `false`.

### Sum elimination

For $v:\gamma\to\llbracket A\rrbracket+\llbracket B\rrbracket$ and branch denotations

$$
m:\gamma\times\llbracket A\rrbracket\to T_b\llbracket C\rrbracket,
$$

$$
n:\gamma\times\llbracket B\rrbracket\to T_b\llbracket C\rrbracket,
$$

use

$$
\gamma\times(\llbracket A\rrbracket+\llbracket B\rrbracket)
\cong
(\gamma\times\llbracket A\rrbracket)
+
(\gamma\times\llbracket B\rrbracket)
$$

followed by $[m,n]$.

## 8. Concrete Writer instance

The current upper-bound effect discipline has a small nontrivial model.

Let

$$
B=\{1_B,w\},
\qquad
1_B\leq w,
\qquad
w\cdot w=w.
$$

In $\mathbf{Set}$ define

$$
T_{1_B}X=X,
$$

$$
T_wX=\mathsf{List}(\mathsf{String})\times X.
$$

The coercion is

$$
\tau_{1_B,w}(x)=([],x),
$$

and graded multiplication at $w\cdot w=w$ concatenates the nested logs:

$$
\mu_{w,w}(\ell_1,(\ell_2,x))
=(\ell_1+\!+\ell_2,x).
$$

Interpret

$$
\mathsf{tell}^T(s)=([s],*).
$$

Then the program

```text
let u <- tell("a") in
let v <- tell("b") in
return true
```

denotes

$$
([\text{"a"},\text{"b"}],\mathsf{true})
\in T_w\mathsf{Bool},
$$

matching the Writer-machine calculation in [Base calculus examples v1](base-calculus-examples-v1.md).

The idempotent grade $w\cdot w=w$ records “may write” rather than an exact number of writes. The Writer payload itself still records their exact ordered sequence.

## 9. Soundness obligations

The immediate theorem is internal reduction soundness:

$$
\Gamma\vdash M:A!b,
\quad
M\longrightarrow M'
\quad\Longrightarrow\quad
\llbracket M\rrbracket=\llbracket M'\rrbracket.
$$

The principal cases use:

- exponential $\beta$-law for `R-Beta`;
- graded monad left unit for `R-Let-Return`;
- coproduct $\beta$-laws for conditionals and cases.

Further obligations are:

1. semantic substitution;
2. coherence under different `T-Sub` derivations;
3. agreement between a chosen base machine and the primitive maps $\beta^T$;
4. adequacy for chosen ground observations;
5. preservation of this semantics when Stage 1 adds free operations.

## 10. Boundary before Stage 1

Before extending the language, check:

- whether bicartesian closure is needed in full or finite products/coproducts plus selected exponentials suffice;
- whether every base model used later has coherent graded strength and subeffect coercions;
- whether base operations are merely chosen morphisms $P\to T_bR$ or should satisfy an algebraicity/naturality interface;
- whether the upper-bound Writer and State examples cover the intended base-effect discipline.

No carrier for free $\Delta$-layers is selected on this page.

