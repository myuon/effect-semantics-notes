# Assumption dependency audit

## Status

**Proof dependency audit for the finite and recursive theorems.** This page records
the first point at which each semantic hypothesis is used. It prevents a
failure to construct graded bind from being misreported as a failure of the
entire language extension.

## 1. Seven strata

### O — operational extension

`OpExt` consists of the new operation syntax, typing rule, evaluation
contexts and exposed-request boundary. It uses `BaseSafetyCert`
and response kernel, but no denotational initial algebra.
Typing and residual-context factorization give `EffectSafetyCert`. The
separate `EmptyFreeCert` additionally assumes no-erasure.

### C — indexed carrier

`CarrierCert` consists of the indexed initial algebras

$$
\alpha_A:\mathcal H_A(\mathsf F A)\cong\mathsf F A,
$$

their return/base/free constructors and coherent weakening. It does not yet
assert a bind on $\mathsf F$.

### M — monadic composition

`MonadExtCert` adds a coherent

$$
\mathsf{baseAct}_{b,d}:T_b(\mathsf F_dA)\to\mathsf F_{bd}A.
$$

Indexed recursion then defines graded bind, strength and the monadic base
embedding.

### F — morphism lifting

`FunctorCert` requires compatible layer maps and `Act-Morphism`. It upgrades
the carrier fold $\mathsf F(q)$ to a strong graded monad morphism and proves
identity and composition.

### R — relation lifting

`RelCert` has two levels. Constructor-wise $\mathsf{Str}_\Delta(R)$ needs
only `CarrierCert` and a base-layer relation. Closure under extended bind also
requires `MonadExtCert` and compatibility of $R$ with the two base actions.

### T — observation and adequacy

`FiniteTTCert` adds $\mathsf{FiniteResponseCert}(\mathcal K)$, a well-founded operational
response tree, the canonical separated observation algebra and closure of the
base pole. The typing fundamental lemma also uses `MonadExtCert`, because
source `let` is interpreted by extended bind.

### H — shallow handling

`ShallowExtCert` adds a handled-operation set $J$, a valid effect transformer
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

1. `BaseSafetyCert + OpExt` preserves operational safety and old-language
   operational behavior.
2. Adding `CarrierCert` gives a coherent indexed semantic carrier with old
   and new generators.
3. Adding `MonadExtCert` makes that carrier a strong graded monad and makes
   the base embedding monadic.
4. Adding `FunctorCert` lifts compatible base morphisms functorially.
5. Adding a graded base relator with `Rel-Act`, together with
   `RelCert + FiniteTTCert`, transports the finite fundamental lemma and
   adequacy.
6. Adding `ShallowExtCert` transports the corresponding operational,
   denotational and observational handler properties.
:::

**Proof.** Each item is respectively Chapter II operational induction,
indexed initiality, the `baseAct` recursion and laws, initial-algebra
uniqueness plus `Act-Morphism`, structural/TT induction, and the four-case
shallow-handler induction. The dependency table records that no later premise
is used in an earlier proof. $\square$

## 4. Consequence for the research question

There are now three distinct answers to “can the base effect system be
extended naturally?”

1. **Operationally: yes**, under the small syntax conditions; no interaction
   law with the denotational monad is needed. No-erasure is used only for the
   additional corollary that a $\Sigma$-free bound cannot expose a $\Sigma$
   request.
2. **As an indexed semantic datatype: yes**, whenever the layer initial
   algebras exist.
3. **As a compositional graded effect semantics: conditionally**, exactly
   when a coherent base action is available, directly or by a sufficient
   construction such as root exposure.

Adequacy and handler compatibility are not additional miracles: after level
3, they require an observation pole and clause compatibility. Thus the first
genuine semantic obstruction is not the existence of free-operation nodes;
it is composition of an opaque old computation with an extended
continuation.

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

The RM entries in the relation and adequacy rows supply the semantic fixed
point and continuity; RT supplies admissible induction.  The elimination row
does not use a domain model, observation reflection or TT reasoning: it is an
operational type-and-boundary invariant over finite unfoldings. Thus partial deep handling is
already definable without EL; only the claim that the whole interface has
disappeared requires exhaustiveness.
