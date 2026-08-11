# Existence of the graded free monad transformer

## Status

**Structural assumption for the finite extension theorem.** The main theorem
assumes the strong graded free monad transformer packages

$$
\widehat T:=\operatorname{FreeT}_\Sigma(T),
\qquad
\widehat S:=\operatorname{FreeT}_\Sigma(S)
$$

and their universal embeddings, free generators and coherent base actions.
This page separates carrier-existence conditions from the additional proof
that those carriers support the required graded monad structure. The older
indexed-carrier and `baseAct` presentation is one implementation route.

## 1. Standard FreeT equation

Ignoring grades for a moment, fix a monad $T$ and an operation-signature
functor $\Sigma$. The standard free monad transformer is the parameterized
initial algebra

$$
\widehat T A
\cong
T(A+\Sigma(\widehat T A)),
\qquad
\widehat T A:=\mu X.\,T(A+\Sigma X).
\tag{FreeT}
$$

Write the two directions as

$$
\mathsf{out}_A:\widehat T A\to T(A+\Sigma\widehat T A),
\qquad
\mathsf{roll}_A:T(A+\Sigma\widehat T A)\to\widehat T A.
$$

Return, the base embedding and the free generators are

$$
\begin{aligned}
\mathsf{return}^{\widehat T}
  &=\mathsf{roll}\circ\eta^T\circ\mathsf{inl},\\
j
  &=\mathsf{roll}\circ T(\mathsf{inl}),\\
\mathsf{op}^{\widehat T}
  &=\mathsf{roll}\circ\eta^T\circ\mathsf{inr}.
\end{aligned}
$$

The base action is canonically derived in this ungraded presentation:

$$
\boxed{
\mathsf{act}^{T,\Sigma}
=\mathsf{roll}\circ\mu^T\circ T(\mathsf{out})
}:
T(\widehat T A)\to\widehat T A.
\tag{FreeT-Act}
$$

Initial-algebra recursion then defines bind. The monad laws follow from
initiality and the monad laws of $T$. This displayed formula is not, by
itself, a definition of the graded action below: its graded analogue must
include the grade decomposition carried by the chosen indexed layer.

## 2. Accessible existence theorem

:::{prf:theorem} Accessible FreeT existence
:label: thm-accessible-freet-existence-v1

Let $\mathcal C$ be locally presentable, with the coproducts used below. If
$T$ and $\Sigma$ are accessible endofunctors and $T$ is a monad, then for
every parameter $A$ the accessible endofunctor

$$
G_A(X)=T(A+\Sigma X)
$$

has an initial algebra. Hence the carriers
$\operatorname{FreeT}_\Sigma(T)A$ exist and are functorial in $A$.
:::

For finitary $T$ and $\Sigma$, the carrier is the colimit of the initial
$\omega$-chain

$$
0\to G_A0\to G_A^2 0\to\cdots.
$$

Thus its elements are finite-depth interaction trees. Recursion in the source
language is not part of this construction.

To obtain a **strong** FreeT in a general category, additionally require that
$T$ and $\Sigma$ carry compatible strengths and that the parameterized
initial-algebra construction is stable under the products used by strength.
In $\mathbf{Set}$ this is explicit for the polynomial examples below.

## 3. First-order operation signatures

For operations $\mathsf{op}_i:P_i\to R_i$, use

$$
\Sigma X=\coprod_iP_i\times X^{R_i}.
$$

If the interface and all $R_i$ are finite, $\Sigma$ is finitary polynomial.
For arbitrary small response sets, it is accessible at a sufficiently large
regular cardinal. Full unbounded powerset branching is outside this simple
criterion.

## 4. Graded form

Let $B$ be the base grade algebra and $\widehat E$ the extended one. Work in
the indexed category $\mathcal C^{\widehat E}$. The graded FreeT equation is a
parameterized initial-algebra equation whose layers record all legal
decompositions of the result bound into base and free-operation factors.

A convenient sufficient package is:

1. $B$ and $\widehat E$ are small;
2. $\mathcal C$ is locally presentable;
3. every $T_b$ is accessible, uniformly below some regular cardinal;
4. $\Sigma$ is accessible;
5. the grade-indexed coproducts and reindexing maps are small;
6. the resulting indexed layer endofunctor is accessible;
7. the parameterized initial algebras support the required strength and
   coherent weakening.

Under these conditions the indexed carriers exist. Carrier existence alone
does not yet produce a `StrongGradedFreeT`. One must additionally construct
graded return, bind, strength, weakening, the universal embedding and free
generators, and a coherent action

$$
T_b(\widehat T_dA)\longrightarrow\widehat T_{b\cdot d}A.
$$

A graded fold/unfold presentation may derive this action by a typed analogue
of `(FreeT-Act)`. If the root grade is externalized as a coproduct, a direct
action or a root-exposure condition may instead be needed.

## 5. Concrete instances in Set

| base monad $T$ | accessibility | FreeT consequence |
|---|---|---|
| Writer $W\times-$ | finitary polynomial | exists for finitary $\Sigma$ |
| Exception $-+\mathsf{Err}$ | accessible polynomial | exists |
| State $S\to(-\times S)$ | accessible at a regular cardinal above $|S|$; finitary when $S$ is finite | exists for small $S$ |
| finite powerset $\mathcal P_{\mathrm{fin}}$ | finitary | exists |
| finite-support SubDist | finitary | exists |
| full powerset $\mathcal P$ | not accessible | not covered |

For concrete Set-level graded tree constructions, the required action
specializes to:

- Writer: concatenate the outer log with the first inner log;
- State: pass the outer final store to the inner computation;
- Exception: propagate an outer error, otherwise continue with the returned
  tree;
- finite SubDist: flatten the distribution of trees by finite probabilistic
  bind.

These direct actions do not require the base functor to preserve coproducts.
In particular State, Exception and finite SubDist generally do not preserve
the grade-indexing coproduct used by the older root-exposure construction.

## 6. Functoriality and comparison

For base morphisms $q:T\Rightarrow S$ preserving the monad structure and the
primitive interpretations, parameterized initiality lifts $q$ to

$$
\widehat q:
\operatorname{FreeT}_\Sigma(T)
\Rightarrow
\operatorname{FreeT}_\Sigma(S).
$$

The lift is the identity on returns and free generators and applies $q$ to
base layers. It preserves identities and composition. For canonical lifts,
compatibility with the chosen actions is proved from their construction,
naturality of $q$, and preservation of multiplication. For arbitrary chosen
extensions it remains the explicit `Act-Morphism` package.

## 7. Main-theorem boundary

The finite theorem therefore assumes:

$$
\mathsf{StrongGradedFreeT}(T,\Sigma,\widehat T)
\land
\mathsf{StrongGradedFreeT}(S,\Sigma,\widehat S).
$$

Accessibility discharges the carrier-existence part of this assumption. The
remaining graded-monad and action fields must be discharged by a concrete
construction, a typed graded fold/unfold theorem, or the indexed-carrier plus
coherent-action route. The theorem does not expose `baseAct` as a second
top-level premise because it is already a field of `StrongGradedFreeT`.
