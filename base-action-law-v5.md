# The base-action law

## Status

**Minimal additional structure isolated.**  The indexed free carrier becomes a
graded monad only when the old base computation can be composed in front of an
already extended computation.  This page specifies that structure and its
laws.

## 1. Definition

For every base grade $b$, extended grade $d$ and value object $A$, a base
action is a natural map

$$
\mathsf{act}_{b,d,A}:
T_b(\mathsf F_dA)\to\mathsf F_{b\cdot d}A.
$$

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

3. **Weakening coherence.** Acting before or after any base/extended
   weakening gives the same map into a common upper bound.
4. **Strength coherence.** Acting on a computation paired with an untouched
   value agrees with base strength followed by the extended strength.
5. **Free-node compatibility.** The action stays before a new free request; it
   does not commute the base segment past that request.

These are the laws of a graded left $T$-module carried by $\mathsf F$.

## 2. Bind from the action

For $m\in\mathsf F_dA$ and $k:A\to\mathsf F_fC$, recurse over the indexed
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

For every continuation $k:A\to\mathsf F_fC$,

$$
j_b(m)\gg=k
=\mathsf{act}_{b,f}(T_bk(m)).
\tag{Act-Embed}
$$

Consequently `Act-Unit` and `Act-Mult` imply that $j$ preserves graded return
and bind.

## 4. Morphism compatibility

For a base morphism $q:T\Rightarrow U$, the lifted morphism exists only when
the target/source actions commute:

$$
\mathsf F(q)_{b\cdot d}\circ\mathsf{act}^{T}_{b,d}
=
\mathsf{act}^{U}_{b,d}\circ
q_b(\mathsf F(q)_d).
\tag{Act-Morphism}
$$

This square is now part of “compatible morphism.”  Monad-morphism laws alone
do not mention $\mathsf F$ and cannot imply it.

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

The main theorem assumes the action abstractly so it does not force all base
effects to admit an algebraic presentation.

## 6. Concrete actions

### Writer

$$
\mathsf{act}(w,t)=w\mathbin{\mathord{+\!+}}t,
$$

prefixing the first Writer segment.  The action laws are word associativity.

### State

Given

$$
u:S\to(\mathsf F_dA\times S),
$$

run $u$ at the current state, obtaining $(t,s')$, then run the first base
segment of $t$ from $s'$.  The action laws are ordinary State bind laws.

### Exception

For $u\in\mathsf F_dA+\mathsf{Err}$, return the contained tree in the left
case and the corresponding terminal base-error layer in the right case.
Short-circuiting proves the action laws.

### Finite SubDist

For $u\in\mathsf{FinSubDist}(\mathsf F_dA)$, flatten the finite mixture of
trees by probabilistic bind.  Finite-sum associativity proves `Act-Mult`.

## 7. Boundary

The present proof does not derive `baseAct` from graded monad laws and indexed
initial algebras alone.  A general construction additionally needs a way to
expose or distribute the opaque $T_b$ layer across the indexed carrier root.
The [root-exposure theorem](base-action-construction-v5.md) gives one
sufficient condition.  Whether there is a model with all the stated indexed
initial algebras but no coherent base action is retained as an open
independence question.
