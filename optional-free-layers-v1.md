# Optional free layers v1

## Status

**Preferred Stage 1 direction under discussion.**

This page adds the upper-bound principle

$$
1\leq\Delta
$$

to the exact baseline of [Free-operation extension v1](free-operation-extension-v1.md). It explains why this is natural, what carrier it forces, and why padding coherence is not automatic.

## 1. Why $1\leq\Delta$ is reasonable

The Stage 0 base effect is already an upper approximation. For example, a pure branch may be widened from $1$ to Writer grade $w$.

Applying the same principle to free operations gives

$$
\frac{
\Gamma\vdash M:A!E
\qquad E\leq F}
{
\Gamma\vdash M:A!F}.
$$

If $1\leq\Delta$, then

$$
\Gamma\vdash\mathsf{return}\;V:A!1
$$

may be widened to

$$
\Gamma\vdash\mathsf{return}\;V:A!\Delta.
$$

Consequently, the optional program

```text
if c then
  choose_Delta(*)
else
  return false
```

can be typed with common effect $\Delta$.

This matches the reading

> The computation may perform a $\Delta$ operation, but is allowed to return without one.

Thus $1\leq\Delta$ is not intrinsically wrong. It selects an upper-bound free-effect language rather than the exact-skeleton language.

## 2. The semantic layer forced by optionality

Let

$$
\mathsf{Op}_\Delta Z
=
\coprod_{\operatorname{op}:P\to R\in\Delta}
P\times Z^R.
$$

An optional layer must distinguish:

1. no $\Delta$ operation at this layer;
2. one exposed operation from $\Delta$.

Define

$$
\mathsf{Layer}_\Delta Z
=
Z+\mathsf{Op}_\Delta Z.
$$

The extended carrier becomes

$$
\boxed{
\widehat T_{b\Delta E}X
=
T_b\bigl(
\mathsf{Layer}_\Delta(\widehat T_EX)
\bigr)
}
$$

or explicitly

$$
T_b\left(
\widehat T_EX
+
\mathsf{Op}_\Delta(\widehat T_EX)
\right).
$$

The right injection interprets a real operation. The left injection interprets padding/skip.

## 3. What the left branch means

The left branch contains

$$
\widehat T_EX,
$$

not merely $X$.

Its meaning is:

> No operation occurred at this optional $\Delta$ boundary; continue with the residual computation of effect $E$.

For example, at grade

$$
\Delta\cdot w
$$

the computation

```text
tell("fallback");
return false
```

is represented by the left branch containing the Writer computation

$$
([\text{"fallback"}],\mathsf{false})
\in T_w\mathsf{Bool}.
$$

A bare $X$ branch could not retain this tail effect.

Hence ordinary effectful sequencing supports

$$
\widehat T_EX+\mathsf{Op}_\Delta(\widehat T_EX),
$$

not

$$
X+\mathsf{Op}_\Delta(\widehat T_EX),
$$

unless a separate operation collapses the entire residual computation to a value.

## 4. Skip is not the handler return clause

The semantic skip map is

$$
\mathsf{skip}_\Delta:
\widehat T_EX
\to
\mathsf{Layer}_\Delta(\widehat T_EX),
$$

given by the left injection.

This says only that one optional layer was unused. It does **not** say that the whole handled computation has returned a value.

Therefore distinguish:

- **layer skip:** consumes one absent $\Delta$ boundary and leaves the tail computation intact;
- **handler return:** runs only when the complete handled computation reaches $\mathsf{return}\;V$, and passes the value $V$ to the return clause.

Conflating these two operations caused the earlier $X$-versus-$K$ confusion.

## 5. Matching, return, and otherwise

For a future selective shallow handler for $\Delta$, there are three operational cases.

### Final return

```text
handle_Delta (return V) with H
  --> H.return(V)
```

The return clause receives a value.

### Matching operation

At an exposed request

$$
\mathcal E[\operatorname{op}_\Delta(V)],
$$

the matching clause receives $V$ and the captured residual context. To remain shallow, invoking that continuation does not automatically reinstall the same matching handler.

### Mismatching operation

At

$$
\mathcal E[\operatorname{op}_\Gamma(V)]
\qquad(\Gamma\neq\Delta),
$$

an exhaustive `otherwise` branch may forward the request.

There are then two distinct forwarding policies:

1. **forward and stop searching:** the continuation is not rewrapped, so a later $\Delta$ is not handled;
2. **forward and keep searching:** the mismatching request is forwarded, but the handler is reinstalled around its continuation.

Policy 2 is shallow for a matching $\Delta$ operation but recursive/searching for unmatched operations. This is a coherent and useful design, but it must be stated explicitly; “shallow” alone does not determine the treatment of unmatched operations.

## 6. Padding semantics

The generating coercion

$$
1\leq\Delta
$$

is interpreted by inserting a skip layer. At a tail $E$, schematically:

$$
\widehat T_EX
\xrightarrow{\mathsf{inl}}
\mathsf{Layer}_\Delta(\widehat T_EX)
\xrightarrow{\eta}
T_1(\mathsf{Layer}_\Delta(\widehat T_EX))
=
\widehat T_{\Delta E}X.
$$

Under a base prefix, map this padding through the outer $T_b$. Under earlier free layers, map it pointwise through their polynomial continuations.

This gives the intended operational meaning: uppercasting does not execute an operation; it records an unused optional boundary.

## 7. The repeated-token coherence problem

Suppose a term already has grade $\Delta$ and is widened to $\Delta\Delta$. There are two possible insertions:

1. insert the absent layer before the existing one;
2. insert it after the existing one.

Semantically these are different maps

$$
\widehat T_\Delta X
\rightrightarrows
\widehat T_{\Delta\Delta}X.
$$

For an existing operation node:

- the first map produces `skip; op`;
- the second produces `op; skip`.

A handler that eliminates layers one at a time can distinguish them. Therefore a proof-irrelevant preorder with a single inequality

$$
\Delta\leq\Delta\Delta
$$

cannot demand that both padding derivations have the same denotation without an additional quotient/coherence law.

This is the main mathematical cost of making every free token freely insertable.

## 8. Four ways to resolve coherence

### Option A — Proof-relevant effect morphisms

Replace the preorder by a category whose:

- objects are effect words;
- morphisms specify an order-preserving embedding of the source free-token skeleton into the target skeleton;
- missing target positions are explicit padding;
- base components carry their base inequalities.

Then the two maps

$$
\Delta\rightrightarrows\Delta\Delta
$$

are distinct morphisms, so their distinct denotations are legitimate.

This is the mathematically cleanest option if layer position remains observable.

### Option B — Canonical padding elaboration

Keep a surface preorder, but elaborate every uppercast to a chosen canonical embedding, for example left-aligned or right-aligned padding.

This is simpler for a language implementation but makes coherence depend on the elaboration algorithm.

### Option C — Quotient padding positions

Declare `skip; op` and `op; skip` observationally equal. This recovers proof irrelevance but weakens the positional layer structure and may conflict with one-layer-at-a-time handlers.

### Option D — Idempotent row effects

Impose

$$
\Delta\Delta=\Delta.
$$

This models presence/absence rather than ordered multiplicity. It is appropriate for effect rows but abandons the free-monoid occurrence structure.

## 9. Recommended working choice

For this research, the most informative direction is:

1. allow optional free layers via $1\to\Delta$;
2. retain ordered multiplicity of free tokens;
3. use proof-relevant word embeddings, at least in the semantic metatheory;
4. permit a surface language to infer/elaborate canonical coercions later;
5. represent a layer by

   $$
   \mathsf{Layer}_\Delta Z=Z+\mathsf{Op}_\Delta Z;
   $$

6. keep layer skip separate from the handler's final return clause.

This turns the grading structure from a preordered monoid into a monoidal category of effect words and embeddings. The base preorder embeds as the proof-irrelevant part of that category.

## 10. Effect on the preservation package

| Property | Expected status with optional layers |
|---|---|
| deterministic operational semantics | preserved; padding is static/elaborated |
| type preservation | preserved if coercion evidence is tracked coherently |
| base conservativity | preserved |
| graded bind | preserved using functorial `Layer` and word-embedding composition |
| Writer/tree adequacy | preserved after adding skip nodes to the tree relation |
| pure-grade reflection | preserved for base grade $1$ |
| exact free occurrence reflection | intentionally lost |
| “may perform $\Delta$” reflection | preserved as an upper-bound theorem |
| handler matching | requires skip/match/otherwise cases |

The generalized interaction tree now has nodes

$$
\mathsf{skip}_\Delta(t)
$$

and

$$
\mathsf{op}_\Delta(p,k).
$$

Operational syntax need not emit explicit skip steps; skip nodes arise from typing/elaboration evidence and disappear when the corresponding layer is handled or forgotten.

## 11. Conclusion

Allowing

$$
1\leq\Delta
$$

is compatible with the intended upper-bound language and likely simplifies user-facing typing and exhaustive handler syntax.

It does not make the mathematics strictly simpler. It requires:

- an optional-layer carrier $Z+\mathsf{Op}_\Delta Z$;
- a distinction between layer skip and final return;
- an explicit forwarding policy for mismatching operations;
- a solution to repeated-token padding coherence.

With proof-relevant word embeddings, these requirements form a coherent candidate rather than an obstruction.

