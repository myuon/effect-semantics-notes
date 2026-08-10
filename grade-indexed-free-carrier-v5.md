# Grade-indexed free carrier

## Status

**Corrected candidate; conditional on indexed initial algebras and a base
flattening law.**  The old
formula

$$
\mu X.\,T_e(A+\Sigma X)
$$

suppressed the fact that a free request changes the residual grade.  It is
adequate as an ungraded mnemonic, but not as the formal carrier used by the
main theorem.  This page replaces it with an initial algebra on
$\widehat E$-indexed families.

## 1. Index category

Let

$$
\widehat E=B*\mathcal D^*
$$

with its compatible preorder.  Work in the category

$$
\mathcal C^{\widehat E}
$$

of $\widehat E$-indexed families.  A family $X$ contains an object $X_e$ for
each bound $e$ and coherent weakening maps

$$
\tau^X_{e,d}:X_e\to X_d
\qquad(e\le d).
$$

Equivalently, $X$ is a functor from the preorder category $\widehat E$ to
$\mathcal C$.  This makes proof-irrelevance of alternative inequality
derivations an explicit coherence condition rather than a silent assumption.

## 2. One-layer endofunctor

For a value object $A$ and indexed family $X$, define the possible outcome
after one finite base segment $b\in B$ by

$$
\mathsf{Step}_{A,X}(b,d)
=
\left(\coprod_{b\le d}A\right)
+
\coprod_{\substack{\Delta\in\mathcal D,\ i\in I_\Delta,\ e\in\widehat E\\
b\cdot\Delta\cdot e\le d}}
P_i\times X_e^{R_i}.
$$

The first summand returns after effects bounded by $b$.  The second exposes a
$\Delta$ request after that base prefix and stores a continuation bounded by
$e$.  Define

$$
(\mathcal H_A X)_d
=
\coprod_{b\in B}T_b\bigl(\mathsf{Step}_{A,X}(b,d)\bigr).
\tag{Indexed-Layer}
$$

All coproduct injections carry their displayed inequality witnesses, modulo
the coherence identifying witnesses with the same induced weakening map.
Functoriality in $X$ acts pointwise on request continuations.

This construction represents exactly the operational order

$$
\text{finite base segment }b
\ ;\ 
\text{return or first free request }\Delta
\ ;\ 
\text{residual computation }e.
$$

It does not claim that every factor in the upper bound executes.

## 3. Definition of the free carrier

Assume every $\mathcal H_A$ has an initial algebra in
$\mathcal C^{\widehat E}$:

$$
\alpha_A:\mathcal H_A(\mathsf F_\Sigma A)
\xrightarrow{\cong}\mathsf F_\Sigma A.
$$

Define

$$
\widehat T:=\mathsf F_\Sigma(T),
\qquad
\widehat T_dA=(\mu\mathcal H_A)_d.
\tag{Indexed-Free}
$$

Throughout this chapter, $\widehat T=\mathsf F_\Sigma(T)$ denotes the
extension of the base model $T$ by the new signature $\Sigma$. We avoid the
bare symbol $\mathsf F$ when the underlying base model matters.

The familiar constructors are derived as follows.

1. **Return.** Choose $b=1$, use $1\le1$, and apply $\eta^T$:

   $$
   A\to\widehat T_1A.
   $$

2. **Base embedding.** For $m\in T_bA$, map its result into the return
   summand with $b\le b$:

   $$
   j_b:T_bA\to\widehat T_bA.
   $$

3. **Free operation.** Choose the empty base prefix and
   $1\cdot\Delta\cdot e\le\Delta\cdot e$:

   $$
   \mathsf{op}_{\Delta,i,e}:
   P_i\times(R_i\to\widehat T_eA)
   \to\widehat T_{\Delta\cdot e}A.
   $$

4. **Weakening.** Functoriality of the indexed family gives
   $\widehat T_eA\to\widehat T_dA$ whenever $e\le d$.

Thus optional requests such as $1\le\Delta$ require no special return node:
return at grade $1$ is transported to grade $\Delta$ by weakening.

## 4. Bind

Indexed initiality alone does not flatten an arbitrary old computation whose
result is already an extended computation.  Require a coherent base action

$$
\mathsf{baseAct}_{b,d,A}:
T_b(\widehat T_dA)\to\widehat T_{b\cdot d}A.
\tag{Base-Action}
$$

It must extend the embedding $j$, respect the multiplication and strength of
$T$, commute with weakening, and distribute through return/free layers.  In
transformer language this is the required distributive/flattening law between
the old graded monad and the indexed free layer.

Fix $k:A\to\widehat T_fC$. Indexed recursion together with `baseAct` defines,
simultaneously in $d$,

$$
(-)\mathbin{\gg=}k:
\widehat T_dA\to\widehat T_{d\cdot f}C.
$$

On a returning base layer, map its values through $k$ and use `baseAct`.  On a request layer
with decomposition

$$
b\cdot\Delta\cdot e\le d,
$$

rebuild the request with continuations $x\mapsto x\gg=k$.  Monotonicity gives

$$
b\cdot\Delta\cdot(e\cdot f)
\le d\cdot f.
$$

The graded unit and associativity laws follow by indexed initiality and the
`baseAct` laws: both sides are algebra morphisms with the same return,
base-layer and free-node actions.  The same argument gives strength and
weakening coherence.

This is a genuine obligation of the current proof: indexed initiality by
itself has not yet supplied `baseAct`.  It can instead be assumed directly,
constructed from a graded theory sum, or derived from the
[root-exposure sufficient condition](base-action-construction-v5.md).  A
strict independence countermodel has not yet been established.

## 5. Corrected existence premise

The premise used by `Free-Transport` is therefore not merely

$$
\forall e,A.\ \mu X.\,T_e(A+\Sigma X)\text{ exists}.
$$

It is:

> For every $A$, the indexed layer endofunctor $\mathcal H_A$ exists, respects
> weakening, and has an initial algebra in $\mathcal C^{\widehat E}$ stable
> under the products used by strength; moreover the carrier has a coherent
> base action `(Base-Action)`.

In $\mathbf{Set}$ with small signatures and the concrete Writer, State,
Exception and finite-subdistribution layers, this is obtained by the ordinary
inductive tree construction and the corresponding base bind.  In a general
base category both existence and `baseAct` are real hypotheses.

## 6. Functorial lifting

Let $q:T\Rightarrow U$ preserve the graded monad structure, weakening and base
primitives.  It induces a natural transformation

$$
\mathcal H_A^T X\to\mathcal H_A^U X
$$

by applying $q_b$ to each outer base layer and acting identically on the
return/free coproduct.  Indexed initiality produces

$$
\mathsf F_\Sigma(q):
\mathsf F_\Sigma(T)\Rightarrow\mathsf F_\Sigma(U).
$$

Identity and composition follow by uniqueness.  The structural graph proof is
also indexed pointwise, so

$$
\mathsf{Str}_\Sigma(\operatorname{Graph}q)
=\operatorname{Graph}(\mathsf F_\Sigma q).
$$

## 7. What this resolves

The corrected carrier now types:

- the operation constructor at $\Delta\cdot e$;
- arbitrary base prefixes before a free request;
- optional requests introduced by weakening;
- bind at $d\cdot f$;
- coherent subeffecting;
- morphism and structural-relation lifting.

It does not remove the need to prove indexed initial algebras, `baseAct`, or
the observation/TT conditions used for adequacy.

## 8. Literature boundary

The use of indexed families follows the standard view of graded monads as
families indexed by a monoidal category.  Graded algebraic theories provide
free graded-monad constructions and sums of theories; flexibly graded
presentations explain why operations whose argument grades differ require
more care than a rigid single-grade signature:

- Satoshi Kura, [Graded Algebraic Theories](https://arxiv.org/abs/2002.06784).
- Katsumata, McDermott, Uustalu and Wu,
  [Flexible Presentations of Graded
  Monads](https://dylanm.org/flexibly-graded-presentations.pdf).

Our $\mathcal H_A$ is a concrete indexed presentation specialized to an old
base segment followed by the first newly added operation; correspondence with
a chosen general theory-sum construction remains a comparison theorem, not an
assumption.
