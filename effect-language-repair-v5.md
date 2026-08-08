# Repairing shallow replacement with effect languages

## Status

**Mechanized candidate repair.** The single-word obstruction and the basic
downward-closed language construction are checked in Lean without axioms.
Compositional integration with the full graded semantic package remains open.

## 1. The obstruction for a single upper word

Let subeffecting be ordered subsequence and let
$\mathsf{replaceFirst}_{\Delta,R}$ replace the first occurrence of $\Delta$
by the response word $R$. The operation is not monotone. Lean verifies

$$
X\Delta\leq\Delta X\Delta
$$

but

$$
\mathsf{replaceFirst}_{\Delta,R}(X\Delta)=XR,
\qquad
\mathsf{replaceFirst}_{\Delta,R}(\Delta X\Delta)=RX\Delta,
$$

and $XR\not\leq RX\Delta$.

The issue is not that the operational shallow handler is ill-defined. The
issue is that a weakened upper word may insert a *phantom earlier* $\Delta$.
Replacing that static occurrence no longer gives an upper bound for replacing
the occurrence selected by a more precise derivation.

## 2. Exact grades still work

For a response-type-indexed Writer/free tree with an exact grade, exhaustive
shallow handling satisfies the expected structural equation:

$$
t : L
\quad\Longrightarrow\quad
\mathsf{sh}_{\Delta,h}(t)
:
\mathsf{replaceFirst}_{\Delta,R}(L).
$$

The matching case uses $R\cdot e$ and the bare continuation. Writer nodes and
other interfaces are rebuilt while recursively searching. Exhaustiveness is
essential at interface granularity: a missing same-interface clause cannot
justify replacing the interface atom.

## 3. Downward-closed trace languages

Replace one may-effect word by a downward-closed language
$\mathcal L$ of possible words:

$$
v\leq w\in\mathcal L
\quad\Longrightarrow\quad
v\in\mathcal L.
$$

A word $e$ embeds as its principal ideal

$$
\downarrow e=\{v\mid v\leq e\}.
$$

Sequential composition is downward closure of pointwise concatenation:

$$
\mathcal L\odot\mathcal M
=
\downarrow\{uv\mid u\in\mathcal L,\ v\in\mathcal M\}.
$$

Lean checks associativity, the principal empty-word unit, monotonicity, and

$$
(\downarrow e)\odot(\downarrow f)=\downarrow(ef).
$$

## 4. Monotone language-level handling

Define

$$
\mathsf{Handle}_{\Delta,R}(\mathcal L)
=
\downarrow\{
  \mathsf{replaceFirst}_{\Delta,R}(v)
  \mid v\in\mathcal L
\}.
$$

This transformer is monotone by construction:

$$
\mathcal L\subseteq\mathcal M
\Longrightarrow
\mathsf{Handle}_{\Delta,R}(\mathcal L)
\subseteq
\mathsf{Handle}_{\Delta,R}(\mathcal M).
$$

It retains the exact result because
$\mathsf{replaceFirst}_{\Delta,R}(e)$ belongs to
$\mathsf{Handle}_{\Delta,R}(\downarrow e)$.

For each finite upper word $e$, Lean also constructs a finite word
$\mathsf{envelope}_{\Delta,R}(e)$ such that

$$
\mathsf{Handle}_{\Delta,R}(\downarrow e)
\subseteq
\downarrow\mathsf{envelope}_{\Delta,R}(e).
$$

Thus a compiler may retain a single-word annotation by accepting a coarse
finite envelope, while the language semantics records the precise monotone
object.

## 5. Consequence for the main theorem

The sharp equation and the general subsumption theorem must be separated.

1. On principal/exact grades, use first-occurrence replacement.
2. On arbitrary weakened annotations, use a certified monotone transformer.
3. Downward-closed trace languages provide one concrete transformer satisfying
   that requirement.

The next formal task is to grade the typed free-tree carrier directly by these
languages and prove that its bind and shallow fold instantiate the revised
`HandlerTypingCert`.
