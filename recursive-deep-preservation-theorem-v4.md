# Recursive deep certificate-transport theorem v4

## Status

**General theorem extracted after the literature audit and concrete instances;
conditional paper-level proof.**  Its construction and adequacy method are
largely imported.  The contribution candidate is the explicit transport
interface and boundary matrix.

## 1. Input package

A `RecursiveDeepBasePackage` consists of three layers.

### Operational layer `RSafety`

- typed deterministic CBV decomposition, allowing infinite reduction;
- substitution and residual-context typing;
- preservation and effect-aware progress;
- classified old base steps/outcomes;
- disjointness of future free-operation syntax;
- coherent propagation of old steps beneath a pending new handler.

### Semantic layer `RModel`

- a pointed/order-enriched strong base monad $T$;
- continuous return, bind, strength and old primitives;
- a selected iteration operator interpreting source recursion;
- existence of the recursive resumption solutions
  $\mathsf{R}_{T,\rho}$;
- agreement between source fixed points and resumption iteration;
- continuous deep-handler functionals with selected solutions.

A complete-Elgot base plus the standard existence hypotheses supplies much of
this layer, but not its operational interpretation.

### Observation layer `RAdequacy`

- an admissible value/computation relation;
- correctness of every old primitive boundary;
- compatibility with return, bind, strength and iteration;
- separated return/old/free observations;
- handler-clause compatibility;
- an explicit declared observation level.

Optional `HandlerInteraction` data is required for exact old grades,
multi-shot resource laws or handler commutation.  It is not hidden inside the
basic package.

## 2. Operational transport

:::{prf:theorem} Recursive deep operational transport
:label: thm-recursive-deep-operational-v4

Under `RSafety`, adjoining nominal first-order operations, unordered may-rows
and exhaustive deep handlers preserves/provides:

1. deterministic extended decomposition;
2. value-type and row preservation;
3. effect-aware progress;
4. empty-new-row safety;
5. deep discharge of a handled interface from every finite execution prefix;
6. exact operational conservativity for old programs.
:::

**Proof idea.**  The local preservation proof is the finite one with recursive
unfolding classified as an old typed step.  Deep discharge is an invariant of
pending handlers: matching continuations reinstall the handler and nonmatching
continuations retain it.  The proof is by induction on finite reduction
prefixes, so divergence causes no difficulty.

No normalization conclusion survives from Chapter I.

## 3. Semantic transport

:::{prf:theorem} Recursive resumption and handler transport
:label: thm-recursive-resumption-handler-v4

Under `RSafety` and `RModel`:

1. $\mathsf{R}_{T,-}$ is a row-refined strong monad;
2. $T$ embeds at empty new row;
3. the selected iteration interprets recursive source functions and extends
   base iteration;
4. new operations are nominal resumption constructors;
5. exhaustive deep handlers are strict continuous selected solutions of the
   deep equations;
6. a $\Delta$-free target contains no finite observable escaping $\Delta$;
7. well-founded computations restrict to the finite-tree semantics.
:::

Items 1--3 are instances of known recursive-resumption results when their
hypotheses apply.  Items 4--7 align that construction with the fixed source
calculus and handler equations.

## 4. Adequacy transport

:::{prf:theorem} Recursive deep adequacy transport
:label: thm-recursive-deep-adequacy-v4

Under all three package layers, every closed well-typed extended computation is
related to its denotation.  Consequently:

1. one-step soundness is preserved;
2. finite return/old-boundary/free-request adequacy is preserved;
3. operational and denotational deep handling correspond;
4. deep row discharge holds operationally and denotationally;
5. bottom/divergence adequacy is preserved when declared by the base package;
6. productive infinite-trace adequacy is preserved only when the base package
   supplies the stronger trace model and relation.
:::

**Proof idea.**  Lift the base relation through the recursive resumption
equation.  Apply the recursive deep fundamental lemma.  The recursion case uses
admissibility or guarded induction; the handler case uses the selected handler
solution and clause compatibility.  Finally apply exactly the observation
reflection field declared by `RAdequacy`.

## 5. Morphism transport

Let $q:T\Rightarrow U$ preserve strong monad structure, old primitives,
selected iteration and the declared observations.  Then the standard
resumption construction lifts it to

$$
\widehat q_\rho:
\mathsf{R}_{T,\rho}\Rightarrow\mathsf{R}_{U,\rho}.
$$

It commutes with compatible deep handlers when their clauses are related by
$q$.  The graph of such a morphism is a special case of the lifted admissible
relation.  This is a preservation result for supplied structure, not a claim
that every monad morphism automatically preserves chosen fixed points.

## 6. Assumption-to-conclusion matrix

| conclusion | `RSafety` | `RModel` | `RAdequacy` | `HandlerInteraction` |
|---|:---:|:---:|:---:|:---:|
| preservation/progress | yes | no | no | no |
| old operational conservativity | yes | no | no | no |
| deep row discharge | yes | no | no | no |
| recursive resumption semantics | no | yes | no | no |
| semantic handler solution | no | yes | no | sometimes |
| finite-boundary adequacy | yes | yes | yes | no |
| bottom/divergence adequacy | yes | yes | Level 2 | no |
| productive infinite traces | yes | trace model | Level 3 | no |
| exact old base grade | no | no | no | yes |
| unrestricted multi-shot resource safety | no | model-specific | no | yes |
| old/new handler commutation | no | no | no | yes |

## 7. Comparison with Chapter I

| property | finite shallow | recursive deep |
|---|---|---|
| normalization | relative finite theorem | absent |
| semantic carrier | well-founded free tree | recursive resumption/domain |
| proof principle | structural induction | admissible/fixed-point or guarded induction |
| nonmatching request | ends matcher | forwards pending handler |
| matching continuation | bare, exactly once | rehandled; ordinary clause may use it many times |
| remove $\Delta$ from may-row | generally impossible | valid for exhaustive $\Delta$-free clauses |
| divergence observation | irrelevant | explicitly Level 2 |
| productive trace | irrelevant | optional Level 3 model |

## 8. Boundary of the theorem

The theorem does not derive from unordered rows and monad laws alone:

- exact transformed old effect grades;
- validity of duplicating linear or external resources;
- commutation of old and new handlers;
- equality of least-fixed-point and coinductive trace models;
- full abstraction;
- productive-trace adequacy from a bottom-only model.

The Writer, State and Exception examples show these are genuine semantic
choices.  They are recorded as explicit optional certificates rather than
being concealed by a stronger “arbitrary base effect” assumption.
