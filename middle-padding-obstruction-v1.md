# Middle-padding obstruction v1

## Status

**Derived obstruction to the naive “free optional extension of any graded monad.”**

The local handler of
[Shallow handler denotation v1](shallow-handler-denotation-v1.md) is canonical
once an optional layer exists. This page asks whether that layer, including the
coercion

$$
be\leq b\Delta e,
$$

can be constructed from an arbitrary base graded monad. The answer is: not from
the graded-monad operations alone.

## 1. The tempting construction

For an alternating word, set

$$
\widehat T_bA=T_bA
$$

and

$$
\widehat T_{b\Delta e}A
=
T_b\left(
  \widehat T_eA+
  \mathsf{Op}_\Delta(\widehat T_eA)
\right).
\tag{Carrier}
$$

The intended interpretation of

$$
be\leq b\Delta e
$$

is the skip map

$$
\mathsf{pad}_{b,\Delta,e}:
\widehat T_{be}A
\to
\widehat T_{b\Delta e}A.
\tag{Pad}
$$

Using `Carrier`, its desired type is

$$
T_{be}A
\longrightarrow
T_b\left(
  T_eA+
  \mathsf{Op}_\Delta(T_eA)
\right)
$$

in the base-only tail case.

## 2. The direction mismatch

A graded monad supplies multiplication

$$
\mu_{b,e,A}:
T_bT_eA
\longrightarrow
T_{be}A.
$$

To construct `Pad` by inserting the left coproduct injection, however, one first
needs

$$
\delta_{b,e,A}:
T_{be}A
\longrightarrow
T_bT_eA,
\tag{Split}
$$

and could then define

$$
\mathsf{pad}_{b,\Delta,e}
=
T_b(\mathsf{inl})
\circ
\delta_{b,e}.
$$

The required $\delta$ points opposite to graded multiplication. It is not part
of a graded monad.

If padding is meant to leave the original computation observationally intact,
the minimum coherence equation is

$$
\mu_{b,e}\circ\delta_{b,e}
=
\mathsf{id}_{T_{be}}.
\tag{Section}
$$

Thus $\delta_{b,e}$ must be a natural section of multiplication.

## 3. Why strength does not solve it

Tensorial strength has shape

$$
A\times T_bB
\to
T_b(A\times B).
$$

It moves values through an existing effectful layer. It does not decompose one
$T_{be}$ computation into a $T_b$ prefix and $T_e$ suffix. Coproduct
preservation and polynomial functoriality likewise act only after the two
layers have already been exposed.

Therefore the assumptions “strong graded monad + coproducts + exponentials” are
still insufficient for middle padding.

## 4. Why proof-relevant embeddings do not solve it alone

Making the effect morphism proof-relevant distinguishes

$$
\Delta\rightrightarrows\Delta\Delta
$$

according to the insertion position. This solves the ambiguity of **which**
padding map is intended.

It does not construct the selected map. Inserting a token between two base
segments still requires `Split`. Hence there are two independent questions:

1. **identity of padding evidence:** which position is selected?
2. **semantic existence:** can the computation be split at that position?

Proof relevance answers only the first.

## 5. Operational reading of the obstruction

A denotation in $T_{be}A$ may have forgotten where the $b$ phase ended and the
$e$ phase began. Graded multiplication is exactly the operation that composes
those phases:

$$
T_bT_eA\xrightarrow{\mu_{b,e}}T_{be}A.
$$

After composition, an arbitrary semantics need not support reconstructing the
boundary. But inserting a free-operation checkpoint at that boundary requires
that information.

This is not merely categorical bureaucracy. For state-like or continuation-like
semantics, a composite computation generally has no canonical factorization
into “before the checkpoint” and “after the checkpoint.” Even when individual
elements admit several factorizations, choosing one naturally and coherently is
additional structure.

## 6. Boundary cases where splitting is available

The obstruction is specifically about arbitrary $b,e$.

### Unit boundary

Monad unit laws provide canonical maps

$$
T_bA\to T_bT_1A
$$

using $T_b\eta$, and

$$
T_eA\to T_1T_eA
$$

using $\eta_{T_eA}$. These split a boundary whose one side has unit grade.

They do not produce $T_{be}A\to T_bT_eA$ for general $b,e$.

### Strongly decomposable graded monad

If every multiplication $\mu_{b,e}$ is an isomorphism, take

$$
\delta_{b,e}=\mu_{b,e}^{-1}.
$$

This is a very strong condition: the graded monad is strong monoidal rather than
merely lax monoidal in its grade argument.

### Chosen split structure

One may postulate natural sections $\delta_{b,e}$ satisfying unit and
coassociativity-like coherence. This gives enough structure for padding, but it
substantially narrows the class of admissible base semantics.

## 7. Four viable research directions

### Direction A — Add split graded-monad structure

Assume maps

$$
\delta_{b,e}:T_{be}\to T_bT_e
$$

with `Section`, unit coherence, and

$$
T_b\delta_{e,f}\circ\delta_{b,ef}
=
\delta_{b,e}T_f\circ\delta_{be,f}
$$

up to the ambient associators.

Then the nested optional-layer construction works directly.

Advantage: closest to the original formula.

Cost: the theorem is no longer about arbitrary graded monads.

### Direction B — Preserve syntactic phase boundaries

Do not immediately collapse adjacent base segments by $\mu$. Grade by raw
segmented words and interpret

$$
[b][e]
$$

as $T_bT_e$, not $T_{be}$. Padding can then be inserted between the two visible
segments.

Advantage: no inverse multiplication is required.

Cost: the extension does not strictly agree with the base semantics
$T_{be}$; a separate flattening morphism via $\mu$ is needed. Conservativity is
lax rather than equality-on-the-nose.

### Direction C — Elaborate padding before denotational composition

Keep the source typing derivation or sequencing syntax as evidence of the
boundary. Insert the optional layer before applying graded multiplication.

Advantage: matches compiler elaboration and avoids splitting an opaque semantic
value.

Cost: semantics becomes derivation-sensitive unless a coherence theorem proves
that different elaborations agree observationally.

### Direction D — Use a genuinely free interaction construction

Build an interaction-tree/free-monad-transformer semantics in which base and
free nodes remain syntactically visible, and only later map it to the chosen base
model $T$.

Advantage: checkpoints and handlers are structurally available; arbitrary $T$
can be a target of interpretation rather than the carrier being extended
internally.

Cost: the resulting semantics is a free refinement over $T$, not automatically
an equality-preserving extension of its carriers.

## 8. Consequence for the original definition

The original definition asks for a $\Delta$-extension together with the map

$$
\widehat T_{be}
\xrightarrow{
\widehat T_{be\leq b\Delta e}
}
\widehat T_{b\Delta e}.
$$

This should be read as **assumed extension structure**, not as something that
follows automatically from $T$ being a graded monad.

The handler equation

$$
H_\Delta
\circ
\widehat T_{be\leq b\Delta e}
=
(c_{\mathsf{val}})^\sharp
$$

is therefore meaningful: it constrains an already supplied padding map. But a
construction theorem must separately explain where that map comes from.

## 9. Revised theorem architecture

The research should separate two results.

### Representation theorem

Under explicit assumptions such as split multiplication, segmented grades, or
a free interaction construction, build

$$
(T,\Sigma_B)\longmapsto\widehat T
$$

with optional free layers and coherent padding.

### Handler theorem

For every such $\widehat T$, exhaustive clauses canonically induce

$$
H_\Delta:
\widehat T_{b\Delta e}A
\to
\widehat T_{be'e}A.
$$

The second theorem was established conditionally in
[Shallow handler denotation v1](shallow-handler-denotation-v1.md). The first is
the genuine remaining construction problem.

## 10. Recommended next experiment

Before choosing a maximally abstract theorem, compare Directions B and D on the
Writer model:

1. segmented Writer layers retain an explicit cut in a log;
2. free interaction trees retain `tell` and free-operation nodes;
3. flatten both to the ordinary Writer observation;
4. check whether handler results agree after flattening;
5. identify exactly which coherence law is needed for independence from the
   chosen segmentation.

This concrete comparison will show whether the desired result is naturally a
strict extension theorem, a lax/conservative translation theorem, or an
adequacy-preserving free refinement theorem.
