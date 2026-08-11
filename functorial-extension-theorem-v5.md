# Functorial free-effect extension and adequacy transport

:::{admonition} Formalization status — abstract packaging
:class: note
**Lean-checked concrete functor and graded package functor.** The
Type-level finite carrier is now bundled by
[`FunctorialFreeExtensionCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FunctorialFreeExtensionCert#doc),
and instantiated by
[`functorialFreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.functorialFreeExtension#doc).
This proves identity, composition, bind naturality, exact graph lifting,
structural relation compatibility and the same-carrier shallow laws in one
declaration. At the abstract boundary,
[`gradedFreeExtensionFunctor`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.gradedFreeExtensionFunctor#doc)
checks the category and functor laws for chosen graded extensions whose arrows
satisfy the explicit `Act-Morphism` square. In the revised paper interface,
these chosen extensions are supplied by `StrongGradedFreeT`. Canonical lifts
prove action compatibility from their construction; the Lean record retains
the explicit square as a lower-level implementation certificate. For the finite-tree model, existence
is now constructed by
[`finiteTreeExtensiblePackage`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.finiteTreeExtensiblePackage#doc),
with initiality and both action equations checked separately.
:::

### Statement inventory

| statement | Lean status | correspondence |
|---|---|---|
| `[FUN.2.1]` finite free-carrier functor | checked at Type/signature level | [`functorialFreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.functorialFreeExtension#doc) |
| `[FUN.2.2]` finite carrier/action existence | constructed for every pair of typed signatures over the one-point grade algebra | [`finiteTreeExtensiblePackage`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.finiteTreeExtensiblePackage#doc), [`StructuralMap.unique`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.StructuralMap.unique#doc), [`finiteTreeActionCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.finiteTreeActionCert#doc) |
| `[PKG.4.1]` chosen graded-package functor | category, `Act-Morphism` closure and functor laws checked; object construction remains conditional | [`gradedFreeExtensionFunctor`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.gradedFreeExtensionFunctor#doc) |
| `[FUN.3.1]` structural relation closure | checked | [`Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc) |
| `[FUN.4.1]` graph equality | checked in both directions | [`Rel.graphMapSignature_iff`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.graphMapSignature_iff#doc) |
| `[FUN.5.1]` structural-to-TT inclusion | checked under layer certificate | [`TTLayerCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerCert.lift#doc) |
| `[FUN.6.1]` shallow compatibility | checked for one shared handler and for distinct value-compatible handlers; heterogeneous TT clauses remain conditional | [`shallow_map_compatible`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_map_compatible#doc), [`Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.shallow#doc) |
| `[FUN.7.1]` finite adequacy transport | checked as fold naturality; the typed-language fundamental lemma remains separate | [`functorialFreeExtension_adequacyTransport`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.functorialFreeExtension_adequacyTransport#doc) |

## Status

**Main recursion-free theorem, conditional on the displayed premises.**  This
page reorganizes Chapters I--III around the original research question.  It
does not replace their definitions or proofs; it states their common result in
the form

$$
S\longmapsto\mathsf{Sh}_\Delta S,qquad
q\longmapsto\mathsf{Sh}_\Delta q,qquad
R\longmapsto\mathsf{Sh}_\Delta R.
$$

The notation $\mathsf{Sh}_\Delta$ hides two distinct constructions:

$$
\mathsf{Sh}_{\Delta,h}(T)
:=
\mathsf{sh}_{\Delta,h}(\mathsf F_\Delta(T)).
$$

$\mathsf F_\Delta$ freely adds the interface.  The structural map
$\mathsf{sh}_{\Delta,h}$ interprets one shallow handling pass.  Functoriality
belongs first to $\mathsf F_\Delta$; handler compatibility is an additional
theorem about the resulting map.

The [assumption dependency audit](assumption-dependency-audit-v5.md) splits
this combined theorem into operational, carrier, monadic, functorial,
relational, observational and handler strata. The revised main premise is the
existence of the two strong graded FreeT packages, including their coherent
actions.

## 1. Category of admissible base packages

Fix a base syntax $L_B$, ordered effect algebra $E_B$, operational graded
model $S$, denotational graded model $T$, their comparison, and a first-order
interface $\Delta$.
Let $\mathbf{ExtBase}^{\mathrm{str}}_\Delta$ have:

- objects $T$ for which $\mathsf{DenotationalModelCert}(L_B,E_B,T)$ holds and
  $\operatorname{FreeT}_\Delta(T)$ exists as a strong graded monad;
- morphisms $q:T\Rightarrow U$ preserving graded return, bind, strength,
  coherent weakening and primitive interpretations; canonical FreeT lifts
  must prove preservation of the chosen actions;
- identities and composition inherited from graded natural transformations.

Let $\mathbf{Free}^{\mathrm{str}}_\Delta$ contain the corresponding finite free
extensions carrying the FreeT fields of `FreeCert`. We assume the required
strong graded FreeT objects exist and the extended preorder does not erase a
visible $\Delta$ factor. Sufficient existence conditions are in
[FreeT existence](graded-freet-existence-v1.md). The full object and morphism definitions are in
[Categories of extensible semantic packages](package-categories-v5.md).

## 2. Object and morphism theorem

:::{prf:theorem} `[FUN.2.1]` Functorial free-effect extension [[Lean: finite instance]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.functorialFreeExtension#doc) [[Lean: graded package laws]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.gradedFreeExtensionFunctor#doc)
:label: thm-functorial-free-extension-v5

There is a functor

$$
\mathsf F_\Delta:
\mathbf{ExtBase}^{\mathrm{str}}_\Delta
\longrightarrow
\mathbf{Free}^{\mathrm{str}}_\Delta
$$

with object action

$$
T\longmapsto
\mathsf F_\Delta(T),qquad
  \mathsf F_\Delta(T)A
  \cong \mu\mathcal H_A
  \quad\text{in }\mathcal C^{\widehat E},
$$

and arrow action

$$
q:T\Rightarrow U
\longmapsto
\mathsf F_\Delta(q):
\mathsf F_\Delta(T)\Rightarrow\mathsf F_\Delta(U).
$$

It satisfies

$$
\mathsf F_\Delta(\mathsf{id}_T)=\mathsf{id}_{\mathsf F_\Delta(T)},
\qquad
\mathsf F_\Delta(r\circ q)
=\mathsf F_\Delta(r)\circ\mathsf F_\Delta(q).
\tag{Functor}
$$

Every output object preserves graded monad laws, strength, coherent
subeffecting, the canonical base embedding and the free generators.
:::

:::{prf:theorem} `[FUN.2.2]` Finite construction witness [[Lean: package]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.finiteTreeExtensiblePackage#doc) [[Lean: initiality]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.StructuralMap.unique#doc)
:label: thm-finite-construction-witness-v5

For every pair of typed algebraic-operation signatures
$(\Sigma_B,\Delta)$, the finite tree carrier constructs an object of the
package category over the one-point grade algebra. Its old-base action obeys
unit, multiplication and value naturality, and its structural fold is the
unique map preserving return, base operations and free operations.
:::

This is an existence theorem rather than another assumption. It covers the
ordinary ungraded algebraic-effect calculus and supplies a reference witness
for the abstract theorem. It does **not** yet construct the indexed carrier for
an arbitrary nontrivial ordered grade algebra: that step additionally needs a
grade-indexed layer construction and a distributive/base-action law compatible
with grade multiplication and weakening.

**Proof.**  Initiality defines the carrier fold and arrow map; the base action
defines composition of an old base layer with an extended continuation.
`Act-Unit` and `Act-Mult` supply the missing unit and associativity cases.
Identity and the two sides of composition are algebra morphisms with the same
actions on returns, base layers and $\Delta$ generators, so initiality makes
them equal.  The remaining fields are exactly `Free-Transport` from Chapter
II. $\square$

Operational conservativity and effect safety are supplied separately by
`BaseSafetyCert + OpExt`. Finite $\mathcal K$-adequacy is a corollary after
restricting to the observed subcategory and adding `FiniteTTCert`; neither is
a field of the structural functor.

Here $\mathcal H_A$ is the indexed base-prefix/free-request layer from the
[grade-indexed carrier construction](grade-indexed-free-carrier-v5.md).
This is the direct answer to the original equations (2) and (3).  It is not a
theorem about every graded monad: existence of the displayed initial algebras
and compatibility of $q$ are real premises.

## 3. Structural relation lifting

For a heterogeneous value relation $R\subseteq X\times Y$, assume a graded
base relator

$$
\overline{T,U}_e(R)\subseteq T_eX\times U_eY.
$$

Write $\mathsf{Compat}(\overline{T,U})$ when this relator is monotone, natural
and closed under return, graded bind, strength, weakening, base primitives and
the two `baseAct` maps. Define $\mathsf{Str}_\Delta R$ inductively:

- related returns contain related values;
- related base layers use $\overline{T,U}_b$ on the recursively generated
  return/free-node payload relation;
- related free nodes have the same operation tag, related parameters and
  pointwise-related continuations.

:::{prf:theorem} `[FUN.3.1]` Compatible-relation lifting [[Lean: structural carrier]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc)
:label: thm-compatible-relation-lifting-v5

If $\mathsf{Compat}(\overline{T,U})$, then

$$
\overline{T,U}:T\rightsquigarrow U
\quad\longmapsto\quad
\mathsf{Str}_\Delta R:
\mathsf F_\Delta T\rightsquigarrow\mathsf F_\Delta U
$$

is closed under the extended return, bind, strength, weakening, old
primitives and new free generators.  It preserves return and separated finite
observation reflection.
:::

**Proof.** Structural induction over the finite free carrier. The base case
uses the relator on the recursively generated payload relation; the free case
uses the pointwise continuation
hypothesis.  Bind closure is a second induction on the left carrier.  Ground
reflection follows by constructor separation and base reflection. $\square$

This is the qualified form of the original equation (4): arbitrary relations
do not lift, but structure-compatible relations do.

## 4. Graph lemma

For a compatible morphism $q:T\Rightarrow U$, use its graph relator, required
for every $f:X\to Y$ to satisfy

$$
\overline{T,U}_e(\operatorname{Graph}f)
=\operatorname{Graph}(U_ef\circ q_{e,X}).
\tag{Base-Graph-Relator}
$$

Write this relator as $\overline q$.

:::{prf:theorem} `[FUN.4.1]` Graph lifting agrees with morphism lifting [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.graphMapSignature_iff#doc)
:label: thm-graph-lifting-v5

For every compatible $q$,

$$
\mathsf{Str}_\Delta(\overline q)
=
\operatorname{Graph}(\mathsf F_\Delta(q)).
\tag{Graph}
$$
:::

**Proof.**  From left to right, induction over the derivation of the lifted
relation shows that its right component is obtained by applying the unique
fold $\mathsf F_\Delta(q)$.  From right to left, induction over the source
free carrier constructs the corresponding return, base-layer or free-node
relation derivation. In the base case use `(Base-Graph-Relator)` with the
recursively induced payload map; in the free case use the induction hypothesis
pointwise on every response. $\square$

Thus the morphism and structural-relation stories are not merely parallel:
the structural construction extends the morphism construction.  This equality
is not asserted for the observational TT-closure introduced next.

## 5. Observational graded TT-lifting

:::{prf:theorem} `[FUN.5.1]` Structural lifting is contained in TT lifting [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.TTLayerCert.lift#doc)
:label: thm-structural-tt-v5

Under `TTLayerCert`, every structurally related pair of finite free trees has
TT-related folds.
:::

The structural relation records how two free carriers were generated.  For
the fundamental lemma and adequacy, choose a grade-indexed observation pole
$\mathcal O_e$ and lift a value relation $V$ by continuation
biorthogonality:

$$
m\mathrel{V^{\top\top}_e}n
\Longleftrightarrow
\forall f\ \forall(k,\ell)\in V^{\top_f}.\quad
m\gg=k\mathrel{\mathcal O_{e\cdot f}}n\gg=\ell.
$$

If the pole is coherent under weakening and closed under base and free
constructors, then

$$
\mathsf{Str}_\Delta(V^{\top\top})
\subseteq V^{\top_\Delta\top_\Delta}.
\tag{Structural-TT}
$$

The inclusion may be strict because TT-closure identifies everything
indistinguishable by the selected observations.  Hence, for a compatible
observation-preserving morphism,

$$
\operatorname{Graph}(\mathsf F_\Delta q)
=\mathsf{Str}_\Delta(\overline q)
\subseteq(\operatorname{Graph}q)^{\top_\Delta\top_\Delta}.
$$

The formal pole, orthogonality and closure conditions are specified in
[Graded TT-lifting and adequacy relations](graded-tt-lifting-v5.md).

## 6. Shallow-handler compatibility

Fix a handler $h$ with a valid effect transformer $\Phi_h$.  A pair of
handlers $(h_T,h_U)$ is $R$-compatible when their return clauses preserve the
value relation and their matching clauses preserve the lifted continuation
relation.

:::{prf:theorem} `[FUN.6.1]` Naturality and relational compatibility of shallow handling [[Lean: compatible handlers]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_map_compatible#doc)
:label: thm-shallow-naturality-v5

For a compatible morphism $q$ and compatible handlers,

$$
\mathsf{sh}^{U}_{\Delta,h_U}\circ\mathsf F_\Delta(q)
=q_h\circ\mathsf{sh}^{T}_{\Delta,h_T},
\tag{Handler-Nat}
$$

where $q_h$ is the induced map between handler result carriers.  More
generally, if inputs are related by $\mathsf{Str}_\Delta R$, their
shallow-handled outputs are structurally related.  If the clauses preserve the
graded TT relation, the outputs are related by the result TT relation.
:::

**Proof.**  Induction over return, base layer, matching request and
nonmatching request.  The matching case is the clause compatibility premise;
the nonmatching case rebuilds the same request and applies the induction
hypothesis to its continuation. $\square$

The theorem deliberately does not claim that every handler is natural.  A
handler that inspects representation-specific base data or violates the
relation need not commute with $q$.

## 7. Fundamental lemma and adequacy transport

Let a graded `TTCert` be generated from a base observation pole that reflects
the selected ground $\mathcal K$-observation, and suppose the extended pole
distinguishes returns, terminal base outcomes and free requests.

:::{prf:theorem} `[FUN.7.1]` Finite fundamental lemma and adequacy transport [[Lean: adequacy fold transport]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.functorialFreeExtension_adequacyTransport#doc)
:label: thm-fundamental-adequacy-transport-v5

Every well-typed recursion-free extended term is related to its denotation by
the graded TT relation. Before applying any ground observation, the lifted
comparison gives

$$
\llbracket M\rrbracket_{\widehat S}
=\widehat q(\llbracket M\rrbracket_{\widehat T}).
\tag{Adequacy-Transport}
$$

The equality/relation is preserved by an $R$-compatible shallow handler. Any
chosen ground observation may then be applied to both sides.
:::

**Proof.**  The typing induction uses the graded TT laws, structural lifting
for free operations and TT-clause compatibility for the handler form.
Reflection is an induction over the finite operational/free tree. Base
segments use `ModelComparisonCert`; free boundaries use the lifted morphism or
relation pointwise on continuations. Constructor separation is needed only
when a later observation theorem reflects tree shape. $\square$

## 8. Exact answer and boundary

The original question now receives the following answer:

> Free first-order operations form a functorial, structurally
> relation-respecting and
> adequacy-preserving extension of every base package satisfying the split
> safety, model and adequacy certificates
> and the finite initial-algebra hypotheses.  Compatible shallow handlers act
> naturally on that extension.  These properties are transported, not
> recreated, from the base structure.

The theorem does **not** provide initial algebras for arbitrary base monads,
lift incompatible morphisms or relations, make arbitrary handlers natural,
infer exact/principal effects, or preserve termination after adding recursion.
Chapter IV replaces finite induction by continuity, admissibility and
fixed-point induction; its result is a further conditional extension of this
recursion-free theorem, not part of functoriality for free operations alone.

## 9. Proof dependencies

| conclusion | indispensable input | detailed source |
|---|---|---|
| object construction and monad laws | polynomial initial algebra, strong graded base | [Chapter II proofs](chapter-2-proof-details-v5.md) |
| functor laws | initiality and compatible morphisms | [Chapter II certificate](chapter-2-certificate-v5.md) |
| structural relation and graph lifting | compatible base relation, structural free carrier | [Chapter II proofs](chapter-2-proof-details-v5.md) |
| observational relation | coherent pole and graded `TTCert` | [Graded TT-lifting](graded-tt-lifting-v5.md) |
| handler naturality | structural/TT-related clauses and effect transformer | [Chapter III proofs](chapter-3-proof-details-v5.md) |
| adequacy transport | `BaseSafetyCert`, `OperationalModelCert`, `DenotationalModelCert`, `ModelComparisonCert`, optional `ObservationAdequacyCert`, graded `TTCert`, branchwise normalization, constructor separation | [Chapter I certificate](chapter-1-certificate-v5.md) |
| recursive/deep extension | continuity, admissibility, fixpoint agreement | [Chapter IV certificate](chapter-4-certificate-v5.md) |
