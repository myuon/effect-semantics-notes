# Functorial free-effect extension and adequacy transport

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
relational, observational and handler strata. In particular, failure to
construct `baseAct` blocks compositional graded bind, but not the operational
extension or the existence of free-operation constructors.

## 1. Category of admissible base packages

Fix a base syntax $L_B$, ordered effect algebra $E_B$, response monad
$\mathcal K$, observation interface, and a first-order interface $\Delta$.
Let $\mathbf{ExtBase}^{\mathrm{str}}_\Delta$ have:

- objects $T$ for which
  $\mathsf{BaseModelCert}(L_B,E_B,T)$ holds and the
  indexed free layers admit initial algebras equipped with a coherent
  $\mathsf{baseAct}$;
- morphisms $q:T\Rightarrow U$ preserving graded return, bind, strength,
  coherent weakening and primitive interpretations, whose induced
  initial-algebra fold also commutes with $\mathsf{baseAct}$;
- identities and composition inherited from graded natural transformations.

Let $\mathbf{Free}^{\mathrm{str}}_\Delta$ contain the corresponding finite free
extensions carrying the carrier and monadic fields of `FreeCert`. We assume the required polynomial initial
algebras and base actions exist and the extended preorder does not erase a
visible $\Delta$ factor.  The full object and morphism definitions are in
[Categories of extensible semantic packages](package-categories-v5.md).

## 2. Object and morphism theorem

:::{prf:theorem} Functorial free-effect extension
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

:::{prf:theorem} Compatible-relation lifting
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

:::{prf:theorem} Graph lifting agrees with morphism lifting
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

:::{prf:theorem} Naturality and relational compatibility of shallow handling
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

:::{prf:theorem} Finite fundamental lemma and adequacy transport
:label: thm-fundamental-adequacy-transport-v5

Every well-typed recursion-free extended term is related to its denotation by
the graded TT relation.
Consequently, for every closed ground term $M$,

$$
\mathsf{run}_{\mathcal K,\Delta}(M)
=
\mathsf{observe}_{\Delta}(\llbracket M\rrbracket).
\tag{Adequacy-Transport}
$$

The equality is preserved after applying an $R$-compatible shallow handler.
:::

**Proof.**  The typing induction uses the graded TT laws, structural lifting
for free operations and TT-clause compatibility for the handler form.
Reflection is
an induction over the finite operational/free tree.  Base segments use
`BaseAdequacyCert`; free boundaries use constructor separation and pointwise
continuation reflection.  Branches are combined by the response monad
$\mathcal K$. $\square$

For $\mathcal K=\mathsf{Id}$ this is ordinary single-result adequacy.  For
$\mathcal K=\mathcal P$ it compares sets of outcomes, and for
$\mathcal K=\mathsf{SubDist}$ it compares outcome probabilities.

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
| adequacy transport | `BaseSafetyCert`, `BaseModelCert`, `BaseAdequacyCert`, graded `TTCert`, branchwise normalization, constructor separation | [Chapter I certificate](chapter-1-certificate-v5.md) |
| recursive/deep extension | continuity, admissibility, fixpoint agreement | [Chapter IV certificate](chapter-4-certificate-v5.md) |
