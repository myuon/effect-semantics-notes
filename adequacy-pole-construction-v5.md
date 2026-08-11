# Non-circular observation pole and adequacy transport

:::{admonition} Lean correspondence
:class: tip
Finite model-comparison transport is **Lean checked** by [`GenericExtensionAlgebra.ModelComparison.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc); recursive pole induction and limit adequacy are checked by [`GenericRecursiveResumption.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc). Observation reflection additionally uses the explicitly chosen pole described below.
:::

## Status

**Corrected proof architecture.**  This page defines the TT pole from the
already supplied base observation and derives the extended observation.  It
does not assume extended adequacy or hide it inside `observeReflect`.

## 1. Base operational/denotational relation

For each ground value relation $V_A$, let

$$
\mathsf{Run}^B_{e,A}
$$

be the set of closed base machine configurations of type $A!e$, and let
$T_e\llbracket A\rrbracket$ be the denotational carrier.  Define the base pole
by

$$
C\mathrel{\mathcal O^B_{e,A}}t
\quad\Longleftrightarrow\quad
\mathsf{run}^B_{\mathcal K}(C)
=\mathsf{observe}^B_T(t).
\tag{Base-Pole}
$$

This is a definition of a heterogeneous relation, not an adequacy assumption
about all programs. The optional `ObservationAdequacyAssumptions` proves that every
closed base term is related to its denotation. Primitive compatibility for
the TT fundamental lemma follows from its `respSound` field.

## 2. Extended observation object

For finite free computations, define the observation family as the initial
solution

$$
\mathsf{Obs}^\Sigma(A)
\cong
\mathcal K\left(
A+\mathsf{Out}_B+
\coprod_{\Delta,i}
P_i\times(R_i\to\mathsf{Obs}^\Sigma(A))
\right).
\tag{Free-Obs}
$$

The three injections represent return, terminal base outcome and exposed free
request.  A request stores its response-indexed continuation observation.  We
require:

1. the signature is small and the finite initial solution exists;
2. $\mathcal K$ supports the finite Kleisli compositions used by the machine;
3. the three outer constructors and operation tags are separated;
4. $\mathcal K$ preserves the injections required for reflection.

For `Id` this is a finite boundary tree; for finite powerset it is a finite set
of such boundaries; for finite subdistributions it is a finitely supported
subdistribution of boundaries.

## 3. Operational run and denotational observation

Define

$$
\mathsf{run}^\Sigma_{\mathcal K}(M)
\in\mathsf{Obs}^\Sigma(A)
$$

by recursion on the well-founded operational response tree:

- a return uses the return injection;
- a terminal base outcome uses the base-outcome injection;
- a free request uses its tag and parameter, and recursively records every
  response continuation;
- primitive branching is combined by Kleisli composition in $\mathcal K$.

Independently, define

$$
\mathsf{observe}^\Sigma_{\mathsf F}:
\mathsf F_eA\to\mathsf{Obs}^\Sigma(A)
$$

by the indexed initial-algebra fold:

- base layers use the base observation;
- return/free nodes use the corresponding separated constructors;
- continuations are folded pointwise.

Neither definition mentions extended adequacy.

## 4. Extended pole

Now define

$$
M\mathrel{\mathcal O^\Sigma_{e,A}}t
\quad\Longleftrightarrow\quad
\mathsf{run}^\Sigma_{\mathcal K}(M)
=\mathsf{observe}^\Sigma_{\mathsf F}(t).
\tag{Extended-Pole}
$$

`observeReflect` is no longer an independent semantic assumption.  It is the
following consequence of constructor separation:

$$
M\mathrel{\mathcal O^\Sigma}t
\land
\mathsf{observe}^\Sigma_{\mathsf F}(t)=\mathsf{returnObs}(v)
\Longrightarrow
\mathsf{run}^\Sigma_{\mathcal K}(M)=\mathsf{returnObs}(v),
$$

and analogously for base outcomes and free requests.

## 5. Pole-closure lemma

:::{prf:lemma} Extended pole closure
:label: lem-extended-pole-closure-v5

Assume `BaseSafety`, `OperationalModel`, `DenotationalModel`,
`ModelComparison`, `ObservationAdequacyAssumptions`,
`FiniteResponseModel`, the existence/separation conditions for `Free-Obs`, and
well-founded finite response trees. Then $\mathcal O^\Sigma$ is closed under
return, base layers, free nodes, weakening and finite $\mathcal K$-branching.
:::

**Proof.** Return and free nodes follow by congruence of the corresponding
constructors. Base layers use `ObservationAdequacyAssumptions.respSound` and its ground
adequacy field.
Weakening changes only the static membership proof and both observation maps
erase it.  Branching uses the Kleisli laws of $\mathcal K$. $\square$

This lemma discharges the former premise
$\mathsf{PoleClosed}_\Sigma(\mathcal O^\Sigma)$ for the canonical pole; users
need supply it only when choosing a coarser, noncanonical observation.

## 6. Fundamental lemma without circularity

The proof chain is:

1. define $\mathcal O^B$ from the already established base observation;
2. construct the graded TT relation $(V_A)^{\top\top}_e$;
3. prove primitive TT compatibility from `respSound`;
4. structurally lift through the indexed free carrier;
5. use the pole-closure lemma to enter the extended TT relation;
6. prove the typing fundamental lemma;
7. instantiate it at the empty environment and the canonical denotation.

The conclusion is

$$
\mathsf{run}^\Sigma_{\mathcal K}(M)
=\mathsf{observe}^\Sigma_{\mathsf F}(\llbracket M\rrbracket).
$$

Thus extended adequacy is the final conclusion, not a disguised hypothesis.

## 7. Scope of the result

For the current main theorem we restrict $\mathcal K$ to a **finite-response
monad**: every primitive response has finite support and the recursion-free
machine tree is well founded.  This covers `Id`, finite powerset and finitely
supported subdistributions.

Countable probability, general powersets and measurable kernels require extra
limit/measurability hypotheses. They are not consequences of
`FiniteResponseModel` as
currently stated and are excluded from the finite theorem.
