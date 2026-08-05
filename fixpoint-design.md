# Fixpoint design constraints

## Status

**Historical Stage 0 constraint.**  The proposed recursive source calculus and
semantic replacement are now developed in [Recursive calculus
v2](recursive-calculus-v2.md), [Recursive resumption semantics
v2](recursive-resumption-semantics-v2.md), and [Recursion preservation
v2](recursion-preservation-v2.md).

将来fixpointを追加する前に、products、functions、coproductsとunrestricted fixed pointsを同じcategorical structureに載せたときのcollapse resultを記録する。

## 1. The relevant collapse theorem

A cartesian category has parameterized fixed points if, for every

$$
f:X\times A\to A,
$$

there is

$$
f^\dagger:X\to A
$$

such that

$$
f\circ\langle\mathsf{id}_X,f^\dagger\rangle=f^\dagger.
$$

Huwig and Poigné proved a no-go result for combining this property with ordinary cartesian closed and coproduct structure:

> A cartesian closed category with fixed points and binary coproducts is inconsistent/degenerate; in particular, all objects become isomorphic.

The original reference is H. Huwig and A. Poigné, “A note on inconsistencies caused by fixpoints in a cartesian closed category,” *Theoretical Computer Science* 73(1), 101–112, 1990, DOI [10.1016/0304-3975(90)90165-E](https://doi.org/10.1016/0304-3975(90)90165-E). The result and its consequence for domain models are summarized by Abramsky and Jung: cartesian closure, the fixed-point property, and categorical coproducts cannot coexist in a non-degenerate category ([Domain Theory, Section 3.2.3](https://www.cs.ox.ac.uk/files/298/handbook.pdf)).

Thus the dangerous combination is not merely a grammar containing `fix` and `+`. It is the semantic demand that all of the following live in one ordinary category:

1. terminal object $1$ and binary products $\times$;
2. exponentials $B^A$, hence cartesian closure;
3. categorical binary coproducts $A+B$;
4. parameterized fixed points for every morphism $X\times A\to A$.

This closely matches the remembered collection $1,+,\times,\to,\mathsf{fix}$.

## 2. The easier collapse with an empty type

If the category also has an initial object $0$, the collapse is immediate.

The identity

$$
\mathsf{id}_0:0\to0
$$

must have a fixed point, giving a global element

$$
1\to0.
$$

Together with the unique map $0\to1$, this makes $0\cong1$. In a cartesian closed category, $A\times-$ preserves colimits, so

$$
A
\cong A\times1
\cong A\times0
\cong0.
$$

Hence every object is isomorphic. This version is also presented as a Huwig–Poigné exercise in Asperti and Longo’s [Categories, Types, and Structures](https://www.cs.unibo.it/~asperti/PAPERS/book.pdf).

At the syntax-as-logic level, the same warning appears more simply: an unrestricted

$$
\mathsf{fix}_A:(A\to A)\to A
$$

at $A=0$ produces

$$
\mathsf{fix}_0(\lambda x.x):0.
$$

This destroys logical consistency. Operationally the term diverges, so this does not by itself mean that a programming language's type checker equates all types. The categorical collapse requires treating the fixed-point equations and coproduct/CCC universal properties together in the same total category.

## 3. Why PCF-like languages still work

General recursion, products, functions, and sums do coexist in useful programming languages. The escape is that their semantics does not require the four structures above to coexist naively on all objects and morphisms.

The standard domain-theoretic comparison is:

- `CPO` can have cartesian closure and ordinary disjoint coproducts, but not every object is pointed, so not every endomorphism has a least fixed point.
- pointed CPOs with continuous maps support least fixed points on every object, but ordinary categorical coproducts are lost; coalesced sums identify bottom points.
- other models put divergence behind a lifting/partiality monad, or interpret recursion only in a designated computation category.

Abramsky and Jung explicitly use this obstruction to motivate coalesced sums and the separation between unpointed and pointed domains ([Domain Theory](https://www.cs.ox.ac.uk/files/298/handbook.pdf)). Nontrivial cartesian fixed-point models themselves are standard; iteration-category models include continuous functions on suitable ordered structures, but their coproduct/additive structure must be treated with care ([Ésik, “Equational properties of fixed-point operations in cartesian categories”](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/831C5B7B816F45ECF4250066C2C3A0FD/S0960129518000361a.pdf/equational_properties_of_fixedpoint_operations_in_cartesian_categories_an_overview.pdf)).

## 4. Consequence for the present calculus

The current calculus already separates

$$
\Gamma\vdash V:A
$$

from

$$
\Gamma\vdash M:A!b.
$$

We should exploit this separation rather than add a pure value-level constant

$$
\mathsf{fix}_A:(A\to A)\to A
$$

uniformly at every value type.

The leading candidate is a **computation-level recursive binder**, schematically

$$
\frac{
\Gamma,x:A\vdash M:A!b
}{
\Gamma\vdash\mathsf{fix}\;x.M:A!b_{\mathsf{rec}}
},
$$

where the exact recursive effect $b_{\mathsf{rec}}$ and operational unfolding rule remain to be designed. Semantically, recursion should live in a pointed/enriched computation structure or behind a partiality/lifting construction, not as fixed points for every morphism of the value CCC.

Another candidate is recursive functions whose application is effectful:

```text
fix f (x : A) = M
```

with a value type such as

$$
A\to(B!b),
$$

while creation of the function remains a value and recursive unfolding happens only when its computation body is applied.

## 5. Decisions for Stage 0

For now:

- keep $1$, products, binary sums, and effectful function types;
- do not add $0$ merely for convenience;
- do not add unrestricted pure $\mathsf{fix}_A:(A\to A)\to A$;
- preserve the value/computation distinction;
- when recursion is added, give divergence/recursion an explicit computation-level semantic home;
- do not assume that coproducts in a pointed computation category are ordinary disjoint coproducts.

These are design constraints, not yet a final recursion rule. The next recursion-specific task is to compare computation-level `fix`, recursive functions, guarded recursion, and a lifting/partiality effect against the intended operational semantics.
