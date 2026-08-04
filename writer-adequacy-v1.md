# Writer adequacy v1

## Status

**Concrete Stage 0 reference theorem.**

This page instantiates the base calculus with Writer, relates its machine semantics to its graded denotation, and isolates properties that a later free-operation/handler extension should preserve.

## 1. Writer instance

Take the effect algebra

$$
B_W=\{1,w\},
\qquad
1\leq w,
$$

with multiplication

$$
1\cdot b=b=b\cdot1,
\qquad
w\cdot w=w.
$$

The only base operation is

$$
\mathsf{tell}:\mathsf{String}\to1,
\qquad
|\mathsf{tell}|=w.
$$

There is no recursion in this instance.

## 2. Writer machine

A configuration is

$$
\langle M,\ell\rangle,
$$

where $M$ is a closed computation and $\ell$ is the log accumulated so far.

Internal reduction lifts to configurations:

$$
\frac{M\longrightarrow M'}
{\langle M,\ell\rangle
\longrightarrow_W
\langle M',\ell\rangle}.
\tag{W-Internal}
$$

Writer responds to the unique active request by

$$
\langle
\mathcal E[\mathsf{tell}(s)],
\ell
\rangle
\longrightarrow_W
\langle
\mathcal E[\mathsf{return}\;*],
\ell+\!+[s]
\rangle.
\tag{W-Tell}
$$

Final configurations are

$$
\langle\mathsf{return}\;V,\ell\rangle.
$$

Write

$$
\langle M,[]\rangle
\Downarrow_W
\langle V,\ell\rangle
$$

when

$$
\langle M,[]\rangle
\longrightarrow_W^*
\langle\mathsf{return}\;V,\ell\rangle.
$$

## 3. Writer denotation

Work in $\mathbf{Set}$ and define

$$
T_1X=X,
\qquad
T_wX=\mathsf{List}(\mathsf{String})\times X.
$$

Subeffect coercion inserts the empty log:

$$
\tau_{1,w}(x)=([],x).
$$

The nontrivial graded multiplication is

$$
\mu_{w,w}(\ell_1,(\ell_2,x))
=(\ell_1+\!+\ell_2,x).
$$

The primitive operation is

$$
\mathsf{tell}^T(s)=([s],*).
$$

For a closed computation

$$
\vdash M:A!b,
$$

its denotation is an element

$$
\llbracket M\rrbracket\in T_b\llbracket A\rrbracket.
$$

## 4. A common observation space

Because a term may be typed at grade $1$ or $w$, compare both in

$$
T_wX=\mathsf{List}(\mathsf{String})\times X.
$$

Define

$$
\mathsf{up}_1(x)=([],x),
$$

$$
\mathsf{up}_w(\ell,x)=(\ell,x).
$$

Thus

$$
\mathsf{up}_b:T_bX\to T_wX
$$

is either the subeffect coercion or the identity.

For a closed configuration at declared grade $b$, define its total observation by prepending the already accumulated machine log:

$$
\mathsf{Obs}_b(\ell,M)
=
\mathsf{prepend}_\ell
(\mathsf{up}_b(\llbracket M\rrbracket)),
$$

where

$$
\mathsf{prepend}_\ell(\ell',x)
=(\ell+\!+\ell',x).
$$

When an intermediate residual term is widened back to the original grade $b$, use the coherent `T-Sub` denotation. This makes the declared grade stable across machine steps even though an already handled `tell` has disappeared syntactically.

## 5. Machine determinism

### Theorem W-001

For every closed well-typed configuration, at most one Writer-machine rule applies, and its successor is unique.

### Reason

By Stage 0 decomposition, a closed computation is uniquely:

1. a return;
2. an internal redex with a unique reduct;
3. a uniquely decomposed request $\mathcal E[\mathsf{tell}(s)]$.

These cases are disjoint. `W-Internal` applies only in case 2 and `W-Tell` only in case 3. $\square$

## 6. Termination

### Theorem W-002

Every closed well-typed recursion-free Writer computation reaches a unique final configuration.

### Proof sketch

Extend the standard reducibility proof for the simply typed call-by-value lambda calculus with one terminating constant computation

$$
\mathsf{tell}(s):1.
$$

At the base computation case, `tell(s)` takes one machine step to `return *`, which is reducible. The function case is the usual logical-relations clause: a closed function value is reducible when applying it to a reducible argument produces a reducible computation. Products, sums, `if`, and `case` use the standard clauses.

The fundamental reducibility lemma follows by induction on typing. Hence no infinite Writer-machine sequence starts from a closed well-typed term. W-001 then gives a unique final configuration. $\square$

This theorem relies essentially on the absence of `fix`. After recursion is added, adequacy must be phrased using partiality, divergence, or a pointed computation semantics.

## 7. One-step semantic invariant

### Lemma W-003

If

$$
\langle M,\ell\rangle
\longrightarrow_W
\langle M',\ell'\rangle,
$$

then

$$
\mathsf{Obs}_b(\ell,M)
=
\mathsf{Obs}_b(\ell',M').
$$

### Internal case

If $M\to M'$, internal reduction soundness gives

$$
\llbracket M\rrbracket=\llbracket M'\rrbracket.
$$

The machine log is unchanged, so the observations are equal.

### `tell` case

Suppose

$$
M=\mathcal E[\mathsf{tell}(s)].
$$

Writer bind interprets the active `tell` as the singleton log $[s]$, followed by the denotation of the evaluation-context continuation. Hence

$$
\mathsf{Obs}_b
(\ell,\mathcal E[\mathsf{tell}(s)])
$$

has log component

$$
\ell+\!+[s]+\!+\ell_{\mathcal E}.
$$

After `W-Tell`, the accumulated log is $\ell+\!+[s]$, while `return *` contributes the empty log. Thus

$$
\mathsf{Obs}_b
(\ell+\!+[s],\mathcal E[\mathsf{return}\;*])
$$

has the same log component

$$
(\ell+\!+[s])+\!+[]+\!+\ell_{\mathcal E}.
$$

Associativity and the empty-list laws make the observations equal; the returned value component is unchanged. $\square$

## 8. Evaluation soundness

### Theorem W-004

If

$$
\langle M,[]\rangle
\Downarrow_W
\langle V,\ell\rangle,
$$

then

$$
\mathsf{up}_b(\llbracket M\rrbracket)
=(\ell,\llbracket V\rrbracket).
$$

### Proof

Iterate W-003 along the finite machine execution. At the final configuration,

$$
\mathsf{up}_b(\llbracket\mathsf{return}\;V\rrbracket)
=([],\llbracket V\rrbracket)
$$

at the residual pure computation, while the accumulated log is $\ell$. Therefore the total observation is $(\ell,\llbracket V\rrbracket)$. $\square$

## 9. Ground adequacy

### Theorem W-005 — Writer adequacy at Bool

Let

$$
\vdash M:\mathsf{Bool}!b.
$$

Then, for $q\in\{\mathsf{true},\mathsf{false}\}$,

$$
\mathsf{up}_b(\llbracket M\rrbracket)
=(\ell,\llbracket q\rrbracket)
$$

if and only if

$$
\langle M,[]\rangle
\Downarrow_W
\langle q,\ell\rangle.
$$

### Proof

- Right-to-left is W-004.
- For left-to-right, W-002 gives a unique evaluation

  $$
  \langle M,[]\rangle
  \Downarrow_W
  \langle q',\ell'\rangle.
  $$

  W-004 gives

  $$
  \mathsf{up}_b(\llbracket M\rrbracket)
  =(\ell',\llbracket q'\rrbracket).
  $$

  Equality of pairs yields $\ell=\ell'$. In $\mathbf{Set}$, the two injections interpreting `true` and `false` are distinct, so $q=q'$. $\square$

This is computational adequacy for the complete ground observation consisting of both the returned Boolean and the ordered Writer log.

## 10. Pure-grade log theorem

### Corollary W-006

If

$$
\vdash M:A!1,
$$

and

$$
\langle M,[]\rangle
\Downarrow_W
\langle V,\ell\rangle,
$$

then

$$
\ell=[].
$$

### Proof

By W-004,

$$
\mathsf{up}_1(\llbracket M\rrbracket)
=([],\llbracket M\rrbracket)
=(\ell,\llbracket V\rrbracket).
$$

Hence $\ell=[]$. $\square$

This is the concrete effect-soundness property of the grade $1$.

## 11. Sequential log law

### Theorem W-007

Suppose

$$
\langle M,[]\rangle
\Downarrow_W
\langle V,\ell_M\rangle
$$

and

$$
\langle N[V/x],[]\rangle
\Downarrow_W
\langle W,\ell_N\rangle.
$$

Then

$$
\left\langle
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N,
[]
\right\rangle
\Downarrow_W
\langle W,\ell_M+\!+\ell_N\rangle.
$$

Operationally this follows because call-by-value evaluates $M$ before entering $N$. Denotationally it is exactly the Writer multiplication

$$
\mu_{w,w}(\ell_M,(\ell_N,z))
=(\ell_M+\!+\ell_N,z).
$$

Thus ordered effect composition is reflected on both sides.

## 12. Contextual soundness

Define the ground Writer observation

$$
\mathsf{observe}(M)=(\ell,q)
$$

when

$$
\langle M,[]\rangle
\Downarrow_W
\langle q,\ell\rangle.
$$

### Theorem W-008

If two terms have equal denotations at the same type and grade, then every well-typed closing program context of result type `Bool` gives them equal Writer observations.

### Reason

Compositionality of denotation turns a program context into a morphism acting on the hole denotation. Equal hole denotations therefore give equal closed denotations. W-005 turns equality of the closed denotations into equality of the log/Boolean observations. $\square$

This is denotational **soundness** for contextual observation. The converse, full abstraction at higher types, is not claimed.

## 13. Preservation interface for later extensions

The Writer example isolates the following properties.

| ID | Property | Stage 0 witness |
|---|---|---|
| WP-1 | deterministic operational decomposition | W-001 |
| WP-2 | termination without recursion | W-002 |
| WP-3 | one-step operational/denotational invariant | W-003 |
| WP-4 | evaluation soundness | W-004 |
| WP-5 | ground adequacy/reflection | W-005 |
| WP-6 | pure-effect reflection | W-006 |
| WP-7 | ordered sequencing compatibility | W-007 |
| WP-8 | contextual soundness | W-008 |

A later free-operation and shallow-handler extension should state exactly which of WP-1--WP-8 it preserves and under which hypotheses.

In particular, the anticipated theorem shape is not merely

$$
T\mapsto\widehat T.
$$

It is a lifting of a package

$$
(\text{machine},T,R,\text{adequacy data})
$$

to

$$
(\widehat{\text{machine}},\widehat T,widehat R,
\text{extended adequacy data}).
$$

Writer provides the first concrete test of that package.

## 14. Limitations

- The proof of W-002 is a standard reducibility argument but is not mechanized.
- W-005 is stated only for ground `Bool` observations.
- The Writer model is not claimed to be fully abstract at higher types.
- Recursion will invalidate total termination and requires a partial adequacy statement.
- No free operation or handler has yet been added.

