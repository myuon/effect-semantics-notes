# Chapter III — denotational shallow handling

:::{admonition} Lean correspondence — shallow denotation
:class: tip
**Lean checked.** Clauses are [`FreeExtension.AffineHandler`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.AffineHandler#doc), denotation is [`FreeExtension.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow#doc), naturality is [`shallow_map`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_map#doc), and relation preservation is [`shallow_rel`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_rel#doc).
:::

## Status

**Semantic construction over `FreeCert`.**  The principal total theorem is for
the affine response fragment.  General continuation-using clauses require an
explicit effect-transformer certificate.

## 1. Input structure

Let

$$
\mathsf F_\Sigma(T)A
\cong
T\bigl(A+\Sigma(\mathsf F_\Sigma(T)A)\bigr)
$$

be the finite free extension from Chapter II.  Its observations distinguish
returns, base outcomes and free operation nodes.

## 2. General shallow algebra

A general shallow handler supplies:

- a return interpretation
  $h_{\mathsf{ret}}:A\to\mathsf F C$;
- for every matching operation, a clause interpretation

$$
h_i:P_i\times(R_i\to\mathsf F A)\to\mathsf F C;
$$

- transparent reconstruction of nonmatching operation nodes.

The continuation argument is bare: it has not been composed with the handler.

## 3. Structural shallow map

Define

$$
\mathsf{sh}_{\Delta,h}:
\mathsf F A\to\mathsf F C
$$

by traversing base layers and nonmatching nodes until the first match:

$$
\mathsf{sh}_{\Delta,h}(\mathsf{return}\,a)
=h_{\mathsf{ret}}(a),
$$

$$
\mathsf{sh}_{\Delta,h}(\mathsf{base}(m))
=
\mathsf{mapBase}(\mathsf{sh}_{\Delta,h},m),
$$

until the outer base computation returns a free node. At a handled node
$i\in J$,

$$
\mathsf{sh}_{\Delta,h}
(\mathsf{op}_{\Delta,i}(p,k))
=h_i(p,k).
$$

At an unhandled node, meaning $\Gamma\neq\Delta$ or
$\Gamma=\Delta$ with $j\notin J$,

$$
\mathsf{sh}_{\Delta,h}
(\mathsf{op}_{\Gamma,j}(p,k))
=\mathsf{op}_{\Gamma,j}
\left(p,\lambda r.\mathsf{sh}_{\Delta,h}(k(r))\right).
$$

There is a structural recursive call on an unhandled continuation. There is
no recursive call on $k$ in the matching equation.  This is the semantic
content of shallowness.

`mapBase` uses functoriality/strength of the outer base layer.  No operation
that inspects an arbitrary element of $T_bA$ is assumed.

## 4. Affine response handler

For response denotations

$$
r_i:P_i\to\mathsf F_{e'}R_i,
$$

define

$$
h_i(p,k)=r_i(p)\mathbin{\gg=}k.
$$

This is exactly the elaboration “compute a response, then invoke the bare
continuation once.”  With identity return and a $\Delta$-free prefix $b$, the
grade action on the principal shape is

$$
\Phi_{\Delta,e'}
(b\cdot\Delta\cdot e)
=b\cdot e'\cdot e.
$$

Soundness for a path that omits the optional request follows from
$1\leq e'$.  The transformer is monotone wherever the extended preorder is
compatible with the displayed replacement.

## 5. General handler effect certificate

For an unrestricted clause, the grades of the clause body and continuation
type alone do not determine a precise output:

- discarding $k$ removes its possible effects;
- one call includes them once;
- several calls may repeat them in clause-defined order.

Therefore a general handler supplies a monotone map

$$
\Phi_h:\widehat E\to\widehat E
$$

together with local proofs that every return, matching and forwarding equation
lands below $\Phi_h(e)$.  The affine theorem constructs this certificate from
$e'$; the general theorem consumes it as data.

## 6. Concrete semantic equations

### Writer

For the Writer example,

$$
\mathsf{sh}
([a],\mathsf{ask}(q,k))
=([a,h])\mathbin{\gg=}k(\mathsf{true}),
$$

so the continuation contributes `[b]` after `[h]` and the final observation is
`[a,h,b]`.

### State

The base State layer evaluates `get` before revealing the `choose` node.  The
handler supplies `not old`; applying the bare continuation threads the current
store through `put(not old)`.  No handler recursion occurs.

### Exception

An outer error is already a terminal base outcome and never reaches a free
node.  A matching free node whose response clause raises maps to the exception
denotation directly.

## 7. Algebraic boundary

The free extension is a monad construction, but a shallow handler is generally
not a monad morphism.  Handling $M\mathbin{\gg=}f$ once is not the same as
handling $M$ and then installing a fresh handler around $f$: the latter may
handle an additional request.  The correct structure is a typed, natural
first-matching transformation satisfying the displayed equations.
