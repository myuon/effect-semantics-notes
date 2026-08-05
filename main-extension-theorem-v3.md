# Main extension theorem v3

## Status

**Current main theorem of the research program, proved conditionally at paper
level.**  It covers both recursion-free and generally recursive bases through a
layered statement.

## 1. Extension problem

Let $\mathcal L_B$ be a typed fine-grain call-by-value base language.  It may
already contain effects, base handlers, and general recursion.

Fix a small family of nominal first-order interfaces

$$
\Sigma
=
\{\operatorname{op}_{\Delta,i}:P_i\to R_i\}.
$$

Construct $\mathcal L_B^{+\Sigma,H}$ by adding:

- source operations $\operatorname{op}_{\Delta,i}(V)$;
- finite unordered may-rows $\rho$ of new interface names;
- exhaustive nominal deep handlers;
- forwarding of nonmatching operations with the pending handler retained;
- reinstallation of the handler around every matching resumption.

The source operation has no explicit continuation argument.  Continuations
arise operationally from the surrounding CBV context.

## 2. Layer A assumptions: `BaseSafety`

Assume:

1. typed substitution and residual-context typing;
2. deterministic classified decomposition into return, step, or old base
   outcome;
3. preservation of old typing information;
4. old constructs are silent in the new free row;
5. old steps/outcomes propagate coherently through pending new handlers;
6. the syntax extension does not add reductions to old terms.

If the base contains general recursion, its unfolding is one of the typed
deterministic old steps.  No normalization assumption is made.

:::{prf:theorem} Main operational extension theorem
:label: thm-main-operational-extension-v3

Under `BaseSafety`, $\mathcal L_B^{+\Sigma,H}$ preserves/provides:

1. deterministic extended decomposition;
2. value-type and unordered-row preservation;
3. effect-aware progress;
4. empty-new-row safety;
5. exhaustive deep discharge;
6. operational conservativity of every old base term.
:::

Deep discharge means that if an exhaustive handler for $\Delta$ has target row
$\omega$ with $\Delta\notin\omega$, no finite execution prefix exposes an
unhandled $\Delta$ outside it.  This remains true when execution diverges.

## 3. Layer B assumptions: recursive resumption semantics

For the semantic conclusions, additionally assume `RecursiveBaseAdequacy`
RA-2--RA-7:

- a pointed/order-enriched base computation model $T$;
- continuous bind and recursive iteration $(-)^\dagger$;
- recursive row-indexed resumptions
  $\mathsf{CRes}_{T,\rho}A$;
- continuous return, bind, weakening, and base embedding;
- separating finite projections or an equivalent guarded observation;
- correct primitive boundary interpretations;
- admissible/guarded typed logical relations;
- continuous/guarded handler functionals and selected fixed points.

:::{prf:theorem} Main recursive denotational extension theorem
:label: thm-main-denotational-extension-v3

Under Layers A and B:

1. $\mathsf{CRes}_{T,-}$ is a row-refined monad;
2. the recursive base semantics embeds at empty new row;
3. recursive source functions are interpreted by iteration;
4. new operations are nominal request constructors;
5. exhaustive deep handlers are selected fixed points of their handler
   functionals;
6. the handled interface is absent from every target finite observation when
   the target row excludes it;
7. the recursive denotation restricts to the well-founded denotation on the
   recursion-free fragment.
:::

The selected fixed point may be a least CPO fixed point, complete-Elgot
iteration, or guarded/corecursive solution modulo the package's observation
equivalence.  The theorem does not identify these models indiscriminately.

## 4. Layer C assumptions: observation reflection

Assume the package's logical relation reflects the declared observation level:

- Level 1: finite return/base outcome/free request;
- Level 2: Level 1 plus bottom/boundary divergence;
- Level 3: productive infinite observable traces.

:::{prf:theorem} Main recursive adequacy-preservation theorem
:label: thm-main-adequacy-extension-v3

Under Layers A--C, every closed well-typed extended computation is related to
its denotation.  Consequently the extension preserves:

1. one-step soundness;
2. Level-1 finite-boundary adequacy;
3. deep-handler operational/denotational correspondence;
4. Level-2 divergence adequacy when supplied by the base package;
5. Level-3 productive-trace adequacy only when supplied by the stronger base
   observation package.
:::

The theorem never promotes a Level-2 base into Level 3 merely by adding free
operations.

## 5. Conservativity

Let

$$
j_A:T A\to\mathsf{CRes}_{T,\varnothing}A
$$

be the supplied base embedding.

:::{prf:theorem} Main base conservativity theorem
:label: thm-main-conservativity-v3

For every old term $M$ containing no new operation or new handler,

$$
\llbracket M\rrbracket_{+\Sigma,H}
=
j(\llbracket M\rrbracket_B),
$$

and its operational steps and old observations are exactly those of
$\mathcal L_B$.
:::

This is syntax and denotation conservativity.  It is not a claim that wrapping
an old computation in an arbitrary new handler is observationally inert; a
nonidentity return clause may change Writer, State, or Exception behavior.

## 6. Morphisms and relations

Let $q:T\Rightarrow U$ preserve:

- return and bind;
- primitive interpretations;
- row/base embeddings;
- recursive iteration,

  $$
  q(f^\dagger)=(qf)^\dagger;
  $$

- the declared finite/divergence observations.

:::{prf:theorem} Main recursive lifting theorem
:label: thm-main-recursive-lifting-v3

Such a $q$ lifts canonically to

$$
\widehat q:
\mathsf{CRes}_{T,\rho}
\Rightarrow
\mathsf{CRes}_{U,\rho},
$$

preserving the row monad, recursive iteration, free requests, weakening, and
compatible deep handlers.

More generally, an admissible/guarded base computation relation compatible with
the same structure lifts to recursive resumptions and related handlers.
:::

A plain monad morphism is sufficient only in the recursion-free theorem.  The
iteration law is a genuine additional recursive hypothesis.

## 7. Concrete corollaries

:::{prf:corollary} Writer, State, and Exception instances
:label: cor-main-concrete-recursive-v3

The partial recursive Writer, global State, and Exception models constructed in
these notes instantiate Layers A--C through Level 2.  Therefore all conclusions
above except productive infinite-trace adequacy hold for those three bases.
:::

Their differing interaction laws remain visible:

- Writer remembers finite output prefixes but collapses infinite output before
  a boundary to bottom;
- State uses global sequential state across resumptions;
- Exception preserves the scope-sensitive noncommutation of old `try` and new
  handlers.

## 8. Recursion-free corollary

If the source has no general recursion, replace recursive resumptions by the
initial algebras

$$
\mu X.\,T(A+\Sigma_\rho X).
$$

Admissible fixed-point induction reduces to structural induction.  If every
closed computation normalizes to a classified boundary, Level-1 adequacy is
unconditional and bottom is unnecessary.

Thus the earlier unordered theorem is a special case/finite fragment of the
main theorem, not a competing result.

## 9. Exact scope of the claim

The theorem says:

> Once a base language exposes enough operational, iterative, observational,
> and relational structure, adding first-order free operations and exhaustive
> deep handlers preserves that structure compositionally.

It does not say:

- every opaque monad admits such an extension;
- the exact old base effect grade is computable from an unordered row;
- arbitrary resources permit multi-shot continuation use;
- old and new handlers commute;
- occurrence counts or operation order are recovered;
- productive infinite traces arise from a bottom-only base model.
