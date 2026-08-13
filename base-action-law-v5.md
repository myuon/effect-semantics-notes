# How the base monad acts on the free extension

## Status

**Strong-FreeT structure and implementation boundary.** The main theorem
assumes a `StrongGradedFreeT` package, which includes a coherent base action.
For the ordinary ungraded FreeT that action is derived from fold/unfold and
base multiplication. A graded construction must either prove the analogous
typed formula or supply the action by another construction. This page records
the common laws.

## 1. Definition

Fix a base model $T$ and a new operation signature $\Sigma$, and write its
free extension as

$$
\widehat T:=\mathsf F_\Sigma(T).
$$

A base action for this particular extension is a natural map

$$
\mathsf{act}^{T,\Sigma}_{b,d,A}:
T_b(\widehat T_dA)\to\widehat T_{b\cdot d}A.
$$

Thus the domain is a base-$T$ computation returning an already extended
$\widehat T$ computation, and the codomain is one flattened extended
computation. The shorter $\mathsf{act}$ notation below refers to this fixed
pair $(T,\Sigma)$.

On the operational side the same notation is used independently:

$$
\widehat S:=\mathsf F_\Sigma(S),
\qquad
\mathsf{act}^{S,\Sigma}_{b,d,A}:
S_b(\widehat S_dA)\to\widehat S_{b\cdot d}A.
$$

The comparison theorem later requires the lifted map
$\widehat q:\widehat T\to\widehat S$ to commute with these two actions.

For the ordinary ungraded FreeT equation from
[FreeT existence](graded-freet-existence-v1.md), it is canonically

$$
\mathsf{act}^{T,\Sigma}
=\mathsf{roll}\circ\mu^T\circ T(\mathsf{out}).
$$

In the graded theorem, `act` is not a separate top-level premise because it is
a field of `StrongGradedFreeT`; its construction is nevertheless an
object-side proof obligation.

It must satisfy the following conditions.

1. **Unit action.** A pure base layer does nothing:

   $$
   \mathsf{act}_{1,d}(\eta^T x)=x.
   \tag{Act-Unit}
   $$

2. **Associative action.** Flattening two old base layers at once agrees with
   flattening the inner and then the outer layer:

   $$
   \mathsf{act}_{b\cdot c,d}\circ\mu^T_{b,c}
   =
   \mathsf{act}_{b,c\cdot d}\circ
   T_b(\mathsf{act}_{c,d}).
   \tag{Act-Mult}
   $$

3. **Weakening coherence.** For $b\le b'$ and $d\le d'$, writing both
   weakening maps as $\tau$,

   $$
   \tau_{bd,b'd'}^{\widehat T}\circ\mathsf{act}_{b,d}
   =
   \mathsf{act}_{b',d'}\circ
   T_{b'}(\tau_{d,d'}^{\widehat T})\circ
   \tau^{T}_{b,b'}.
   \tag{Act-Weaken}
   $$

4. **Strength coherence.** With right strength $\mathsf{st}$,

   $$
   \mathsf{st}^{\widehat T}\circ(\mathsf{act}_{b,d}\times\mathsf{id})
   =
   \mathsf{act}_{b,d}\circ
   T_b(\mathsf{st}^{\widehat T})\circ\mathsf{st}^{T}.
   \tag{Act-Strength}
   $$

Naturality in the value object is implicit in all four laws. Preservation of
free generators is a condition on a chosen FreeT fold or morphism, not an
additional equation of a bare $T$-module action. In a concrete tree
presentation it says that prefixing an old base layer rebuilds the first free
request without commuting that layer past the request.

These are the laws of a graded left $T$-module carried by
$\widehat T=\mathsf F_\Sigma(T)$.

## 2. Bind from the action

For $m\in\widehat T_dA$ and $k:A\to\widehat T_fC$, recurse over the indexed
free carrier.  A return is sent to $k(a)$.  For an outer base layer
$u\in T_b(-)$, recursively transform its return/free alternatives and apply
$\mathsf{act}_{b,-}$.  A free node is rebuilt with continuations
$r\mapsto k_r\gg=k$.

The action laws give the graded bind equations.  In particular `Act-Mult` is
exactly the missing case in associativity when both sides begin with opaque
base computation.

## 3. Compatibility with base embedding

The canonical embedding is

$$
j_b(m)=\mathsf{act}_{b,1}(T_b(\mathsf{return})(m)).
$$

For every continuation $k:A\to\widehat T_fC$,

$$
j_b(m)\gg=k
=\mathsf{act}_{b,f}(T_bk(m)).
\tag{Act-Embed}
$$

Consequently `Act-Unit` and `Act-Mult` imply that $j$ preserves graded return
and bind.

## 4. Morphism compatibility

For a base morphism $q:T\Rightarrow U$, put
$\widehat T=\mathsf F_\Sigma(T)$ and
$\widehat U=\mathsf F_\Sigma(U)$. The lifted morphism
$\widehat q:\widehat T\Rightarrow\widehat U$ is compatible when the
target/source actions commute:

$$
\widehat q_{b\cdot d}\circ\mathsf{act}^{T,\Sigma}_{b,d}
=
\mathsf{act}^{U,\Sigma}_{b,d}\circ
q_b(\widehat q_d).
\tag{Act-Morphism}
$$

For arbitrary chosen extensions this square is an explicit package. For
a canonical FreeT lift it is a derived theorem once the construction of both
actions and preservation of multiplication have been proved. Monad-morphism
laws alone, without that chosen FreeT structure, do not state the square.

## 5. Ways to obtain the action

There are three valid routes.

1. **Concrete operational carrier.** Define the action directly by running
   the old computation until it returns an extended tree, then continue that
   tree.  Writer, State, Exception and finite SubDist use this route.
2. **Distributive law.** Supply a grade-shifting distributive law that lifts
   every $T_b$ to algebras of the indexed layer functor.  The induced map on
   the initial algebra is `act`.
3. **Sum of graded theories.** Present the old effects and new operations in a
   combined graded algebraic theory.  Its free model carries the old-theory
   action by construction.

The main theorem assumes `StrongGradedFreeT`, which packages the action but
does not force one particular construction of it.

## 6. Concrete actions

### Writer

$$
\mathsf{act}(w,t)=w\mathbin{\mathord{+\!+}}t,
$$

prefixing the first Writer segment.  The action laws are word associativity.

### State

Given

$$
u:S\to(\widehat T_dA\times S),
$$

run $u$ at the current state, obtaining $(t,s')$, then run the first base
segment of $t$ from $s'$.  The action laws are ordinary State bind laws.

### Exception

For $u\in\widehat T_dA+\mathsf{Err}$, return the contained tree in the left
case and the corresponding terminal base-error layer in the right case.
Short-circuiting proves the action laws.

### Finite SubDist

For $u\in\mathsf{FinSubDist}(\widehat T_dA)$, flatten the finite mixture of
trees by probabilistic bind.  Finite-sum associativity proves `Act-Mult`.

## 7. Boundary

The ordinary ungraded FreeT route derives `baseAct` directly. In the graded
setting the corresponding typed construction is part of establishing
`StrongGradedFreeT`. If one instead begins
with the older carrier whose root grade is externalized as a coproduct, graded
monad laws and indexed initial algebras alone do not derive it. That
representation additionally needs a way to expose or distribute the opaque
$T_b$ layer across the indexed carrier root.
The [root-exposure theorem](base-action-construction-v5.md) gives one
sufficient condition.  Whether there is a model with all the stated indexed
initial algebras but no coherent base action is retained as an open
independence question.
