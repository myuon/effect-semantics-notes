# Assumption dependency audit

:::{admonition} Review role
:class: note
This page is an assumption audit, not an additional main theorem. Rows linking to declarations are **Lean checked**; the stratification into O/C/M/F/R/T/H is a **Paper abstraction** used to expose which conclusion consumes which hypothesis.
:::

## Status

**Proof dependency audit for the finite and recursive theorems.** This page records
the first point at which each semantic hypothesis is used. It prevents a
failure to construct graded bind from being misreported as a failure of the
entire language extension.

## 1. Seven strata

### O — operational extension

`OpExt` consists of the new operation syntax, typing rule, evaluation
contexts and exposed-request boundary. It uses `BaseSafety`
and response kernel, but no denotational initial algebra.
Typing and residual-context factorization give `EffectSafety`. The
separate `NoErasureCondition` additionally assumes no-erasure.

### C — graded FreeT existence

`FreeTExistence` supplies the parameterized initial algebras

$$
\widehat T=\operatorname{FreeT}_\Sigma(T),
\qquad
\widehat S=\operatorname{FreeT}_\Sigma(S),
$$

including the strength and coherent weakening required by the graded theorem.
Accessible sufficient conditions are isolated in
[FreeT existence](graded-freet-existence-v1.md).

### M — monadic composition

`MonadExtensionLaws` is included in `StrongGradedFreeT`. For the ordinary ungraded
FreeT its action is derived from the standard equation

$$
\mathsf{act}=\mathsf{roll}\circ\mu^T\circ T(\mathsf{out}).
$$

The graded package must supply a typed construction and laws for this action;
carrier initiality alone is insufficient. `M` remains a proof stratum, but is
not a separate top-level hypothesis because it is bundled by
`StrongGradedFreeT`.

### F — morphism lifting

`FunctorialityLaws` lifts a base monad morphism through the two FreeT initial
algebras. For canonical lifts, `Act-Morphism` follows from the chosen action
construction and preservation of base multiplication. For arbitrary package
arrows it is an explicit package. Identity and composition follow from
uniqueness.

### R — relation lifting

`RelationLaws` has two levels. Constructor-wise $\mathsf{Str}_\Delta(R)$ needs
only `CarrierStructure` and a base-layer relation. Closure under extended bind also
requires `MonadExtensionLaws` and compatibility of $R$ with the two base actions.

### T — model comparison, observation, and adequacy

`ModelComparison` first lifts the denotational-to-operational morphism (or
relation) through the free carrier. `FiniteTTClosure` is an optional later layer:
it adds a well-founded operational tree, a separated observation algebra, and
closure of the selected pole. The typing fundamental lemma also uses
`MonadExtensionLaws`, because source `let` is interpreted by extended bind.

### H — shallow handling

`ShallowExtensionLaws` adds a handled-operation set $J$, a valid effect transformer
and structural/TT clause compatibility. Its operational safety part depends
only on `OpExt`; denotational commutation and handled adequacy depend on M, R
and T. Exhaustiveness $J=I_\Delta$ is required only by interface-level
elimination, not by safety or adequacy.

## 2. Dependency table

| conclusion | O | C | M | F | R | T | H |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| substitution, preservation, request decomposition | ✓ |  |  |  |  |  |  |
| old-language operational conservativity | ✓ |  |  |  |  |  |  |
| exposed-request effect factorization | ✓ |  |  |  |  |  |  |
| no request under a $\Sigma$-free bound | ✓ + no-erasure |  |  |  |  |  |  |
| return/base/free semantic constructors |  | ✓ |  |  |  |  |  |
| coherent semantic weakening |  | ✓ |  |  |  |  |  |
| extended graded bind and strength |  | ✓ | ✓ |  |  |  |  |
| denotational base conservativity |  | ✓ | ✓ |  |  |  |  |
| carrier map induced by a base map $q$ |  | ✓ |  |  |  |  |  |
| lifted map is a graded monad morphism |  | ✓ | ✓ | ✓ |  |  |  |
| constructor-wise structural relation |  | ✓ |  |  | ✓ |  |  |
| structural relation closed under bind |  | ✓ | ✓ |  | ✓ |  |  |
| graph law for compatible morphisms |  | ✓ | ✓ | ✓ | ✓ |  |  |
| finite fundamental lemma and adequacy | ✓ | ✓ | ✓ |  | ✓ | ✓ |  |
| operational handler preservation | ✓ |  |  |  |  |  | ✓ |
| handler denotational commutation | ✓ | ✓ | ✓ |  | ✓ |  | ✓ |
| handled adequacy | ✓ | ✓ | ✓ |  | ✓ | ✓ | ✓ |

Here a check means that the column supplies a premise not already contained
in an earlier named stratum. `F` is not required for adequacy of a single
model; it is required for the original object-and-morphism transport claim.

## 3. Refined preservation theorem

:::{prf:theorem} Layered recursion-free preservation
:label: thm-layered-preservation-v5

For the fixed Chapter-I language and first-order interface $\Delta$:

1. `BaseSafety + OpExt` preserves operational safety and old-language
   operational behavior.
2. Adding `FreeTExistence` gives the two extended strong graded monads,
   old embeddings and new generators.
3. The FreeT fold/unfold equation derives `MonadExtensionLaws`, including the base
   action and graded bind; it is not an extra existence premise.
4. Adding `FunctorialityLaws` lifts compatible base morphisms functorially.
5. Adding a graded base relator with `Rel-Act`, together with
   `RelationLaws + FiniteTTClosure`, transports the finite fundamental lemma and
   adequacy.
6. Adding `ShallowExtensionLaws` transports the corresponding operational,
   denotational and observational handler properties.
:::

**Proof.** Each item is respectively Chapter II operational induction,
FreeT initiality, construction of the chosen action and its laws, initial-algebra
uniqueness, structural/TT induction, and the four-case
shallow-handler induction. The dependency table records that no later premise
is used in an earlier proof. $\square$

## 4. Consequence for the research question

There are now three distinct answers to “can the base effect system be
extended naturally?”

1. **Operationally: yes**, under the small syntax conditions; no interaction
   law with the denotational monad is needed. No-erasure is used only for the
   additional corollary that a $\Sigma$-free bound cannot expose a $\Sigma$
   request.
2. **As a standard graded FreeT: yes under the stated existence package**, for
   example locally presentable/accessibility hypotheses plus compatible
   strength.
3. **As an alternative external-root representation: conditionally**, when
   that representation also constructs the canonical action, directly or by
   a sufficient condition such as root exposure.

Adequacy and handler compatibility are not additional miracles: after level
3, they require an observation pole and clause compatibility. Thus the first
genuine semantic obligation is existence of the strong graded FreeT. Once it
exists, composition with an extended continuation is part of its derived
structure.

## 5. Recursive refinement

Chapter IV does not add a single all-purpose recursion hypothesis.  It splits
the recursive extension into five independent strata:

- **RS — recursive safety:** typing of unfolding and support-wise progress;
- **RM — recursive model:** pointed $\omega$-cpos, continuity, least fixed
  points and the recursive resumption solution;
- **RT — recursive TT:** an admissible pole and fixed-point compatibility;
- **EC — effect closure:** a monotone iteration closure $K$ compatible with
  the handler transformer;
- **RO — recursive observation:** reflection at one explicitly selected
  level (finite boundary, divergence, or productive infinity).

Interface elimination is a sixth, orthogonal strengthening **EL**: the handler
is exhaustive, its outward clauses are $\Delta$-free, transparent forwarding
keeps the handler installed, and resumed computations are handled again.

| recursive conclusion | RS | RM | RT | EC | RO | EL |
|---|:---:|:---:|:---:|:---:|:---:|:---:|
| recursive preservation and progress | ✓ |  |  |  |  |  |
| derived-deep least-fixed-point equations |  | ✓ |  |  |  |  |
| recursive handler relation |  | ✓ | ✓ |  |  |  |
| adequacy at the declared level |  | ✓ | ✓ |  | ✓ |  |
| iteration-closed effect bound |  |  |  | ✓ |  |  |
| outward elimination of $\Delta$ | ✓ |  |  |  |  | ✓ |

Every row additionally inherits the matching finite Chapter-III package
(safety, semantics, relation, adequacy, or handler typing). The RM entries in
the relation and adequacy rows supply the semantic fixed
point and continuity; RT supplies admissible induction.  The elimination row
does not use a domain model, observation reflection or TT reasoning: it is an
operational type-and-boundary invariant over finite unfoldings. Thus partial deep handling is
already definable without EL; only the claim that the whole interface has
disappeared requires exhaustiveness.
