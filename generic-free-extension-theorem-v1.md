# Generic finite free-extension theorem

:::{admonition} Canonical checked abstraction
:class: tip
Every construction and theorem claimed on this page has an individual
generated-API link. There is deliberately no overall structure collecting
them: the monad, base embedding, signature map, structural relation, shallow
handler, and fold laws are independent declarations. Read the concrete
Chapter-II programs before this abstraction; see the [dependency
map](review-guide.md#chapter-ii-free-operations).
:::

## Status

**Mechanized in Lean.** This page isolates the finite abstract construction
that was previously missing from the structure-preservation theorem.

## 1. Why a bare monad is not enough

An arbitrary monad $T$ does not, by itself, expose a functorial one-step shape
through which a recursively defined free-operation tree can be traversed.
Accordingly, the theorem makes the necessary additional information explicit:
the old base effects are presented by a typed algebraic-operation signature
$\Sigma$, and the newly adjoined operations by a second signature $\Delta$.

A signature consists of an operation type and a response family:

$$
\Sigma=(\mathsf{Op}_\Sigma,\mathsf{Resp}_\Sigma),
\qquad
\Delta=(\mathsf{Op}_\Delta,\mathsf{Resp}_\Delta).
$$

Parameters are stored in the operation itself.  The response family specifies
the type accepted by its continuation.

## 2. The carrier `[GF.2.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc)

The finite extension is the initial tree

$$
\mathsf{Ext}_{\Sigma,\Delta}(A)
::=
\mathsf{return}(A)
\mid
\mathsf{base}(o,\mathsf{Resp}_\Sigma(o)\to\mathsf{Ext}_{\Sigma,\Delta}(A))
\mid
\mathsf{free}(p,\mathsf{Resp}_\Delta(p)\to\mathsf{Ext}_{\Sigma,\Delta}(A)).
$$

Lean defines this carrier as
[`FreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc).
Structural recursion defines `bind`; Lean proves both unit laws and
associativity.

The old carrier is the special case with an empty free signature.  There is a
canonical embedding

$$
\iota:\mathsf{Ext}_{\Sigma,\varnothing}(A)
\longrightarrow\mathsf{Ext}_{\Sigma,\Delta}(A).
$$

Every embedded tree carries a `BaseOnly` witness, and erasing along this
witness is a left inverse of $\iota$.  The embedding also preserves `bind`.
Thus old computations do not acquire new requests merely by adjoining
$\Delta$.

## 3. Functorial action and structural relations `[GF.3.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_comp#doc)

A typed signature morphism maps operations forward and responses
contravariantly.  Lean constructs its action on the whole tree and proves

$$
\mathsf{Ext}(\mathrm{id})=\mathrm{id},
\qquad
\mathsf{Ext}(g\circ f)=\mathsf{Ext}(g)\circ\mathsf{Ext}(f),
$$

as well as compatibility with `bind`.  See
[`mapSignature_id`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_id#doc)
and
[`mapSignature_comp`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.mapSignature_comp#doc).

Heterogeneous relations between base operations, free operations, responses
and return values lift structurally to trees.  The lifted relation is closed
under `bind`; the graph of a signature morphism agrees with its structural
map.

## 4. Shallow handling `[GF.4.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow#doc)

An affine handler supplies an optional response tree for each free operation.
Base operations and missing clauses are forwarded recursively.  At the first
operation with a clause, the clause tree is bound to the bare continuation and
the handler terminates.  This is exactly the forwarding shallow semantics used
in the current source calculus.

Lean proves map naturality and preservation of every structural result
relation separately; see
[`shallow_map`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_map#doc)
and [`Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.shallow#doc).

### What the structural relation does

Given a relation $R\subseteq A\times B$, `FreeExtension.Rel R` relates two
operation trees when they have matching base/free nodes and their returned
values are related by $R$; continuations must be related pointwise for every
response. Thus it lifts a relation on results to a relation on computations.
The main uses are [`Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc), which proves compatibility with sequencing, and `Rel.shallow`, which proves compatibility with shallow handling. It is a proof device for simulations and logical relations, not extra runtime data and not part of the definition of a monad.

## 5. Folding into an arbitrary model `[GF.5.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.fold_bind#doc)

Let $T$ be a target monad equipped with interpretations of every operation in
$\Sigma$ and $\Delta$.  If those interpretations distribute over `bind`, the
structural fold

$$
\mathsf{fold}_T:\mathsf{Ext}_{\Sigma,\Delta}(A)\to T(A)
$$

is a monad morphism: it preserves `return` and `bind`.  This is checked by
[`GenericExtensionAlgebra.fold_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.fold_bind#doc).

If $q:S\Rightarrow T$ preserves the monad operations and commutes with every
base/free operation interpretation, then

$$
q(\mathsf{fold}_S(t))=\mathsf{fold}_T(t).
$$

The exact theorem is
[`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc).

Separately, if a relation $R$ is preserved by return and by each base/free
operation layer, then

$$
R(\mathsf{fold}_S(t),\mathsf{fold}_T(t))
$$

for every finite extended tree.  This is
[`GenericExtensionAlgebra.Relation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Relation.lift#doc).
The morphism and logical-relation theorems are therefore distinct, as required
by the research question.

### Observation-indexed TT-lifting `[GF.5.2]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerAssumptions.lift#doc)

The formalization also keeps structural relation lifting distinct from
observational closure.  Given a heterogeneous observation family, Lean defines
orthogonal continuation pairs and the induced biorthogonal relation
$V^{\top\top}$.  Return values enter this relation from orthogonality alone.
The remaining local package asks separately that every base and free
operation interpretation preserve $V^{\top\top}$.

Under precisely those local conditions, every structurally related pair of
free-extension trees has TT-related folds.  See
[`GenericExtensionAlgebra.TTLayerAssumptions.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerAssumptions.lift#doc).
Thus the formal theorem does not silently infer adequacy from a structural
relation: the observation-sensitive premise remains visible.

### Finite model-comparison transport `[GF.5.3]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc)

An operational model is presented as a second algebra for the same base/free
signatures. A comparison map from the denotational algebra must
preserve `pure`, `bind`, and the interpretations of every base and free
operation.  These are local one-layer equations, not a global adequacy
assumption.  Lean then derives

$$
q(\mathsf{fold}_D(t))=\mathsf{fold}_O(t)
$$

for every finite extended computation, including the restriction to embedded
old-language trees.  See
[`GenericExtensionAlgebra.ModelComparison.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc).

## 6. Concrete bases

Writer is proved isomorphic to the generic construction: translations in both
directions are inverse and the forward translation preserves `bind`.  State
uses typed operations `get : Bool` and `put(b) : Unit`; Exception uses
`raise(e) : Empty`, making its non-resumability explicit.  All three receive
the same generic finite package.

For Writer, the operational target is the partial outcome
$\mathsf{Option}(\mathsf{List}(\mathsf{Val})\times A)$.  `tell` prefixes the
log and an unhandled free operation produces no closed outcome.  This algebra
instantiates the generic adequacy package, and Lean proves that its fold
is extensionally equal to the pre-existing `WriterTree.runClosed`:
[`genericWriterOperationalInterpretation_writerToGeneric`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterOperationalInterpretation_writerToGeneric#doc).

## 7. Recursive continuation of this theorem

The base-independent recursive resumption syntax and least-fixed-point
transport have now been formalized. See the
[generic recursive resumption theorem](generic-recursive-resumption-theorem-v1.md).
Writer, Exception, and State instantiate its observer obligations. State uses
an honest state-transformer outcome and joins the finite witnesses from both
`get` response branches.

What still cannot be obtained from this finite theorem is an operation
signature extracted automatically from an opaque monad. Such an extraction
needs additional traversable/container structure or a distributive law.
