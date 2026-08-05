# Main theorem v3: novelty audit

## Status and scope

This is a **claim-by-claim overlap audit**, not a claim that no closer work exists.
The search was performed against primary papers known to be close to the current
construction.  The safe conclusion is therefore:

> several mathematical layers of Main theorem v3 are established prior art;
> any eventual contribution must be stated as a sharper theorem about transporting
> an existing language's proof package, or as a boundary theorem showing why that
> transport cannot be stronger.

The main theorem should not currently be advertised as a new resumption monad, a new
handler semantics, or the first generic safety or adequacy theorem for effect handlers.

## Result-by-result comparison

| Component of our theorem | Closest established result | Audit verdict |
|---|---|---|
| Add a free algebraic signature to a base monad | free models, coproducts of monads, free-monad transformers | **Known construction** |
| Interpret a handler by a fold/algebra | handlers as induced homomorphisms from a free model | **Known construction** |
| Forward unhandled operations modularly | modular algebraic effects and free-monad-transformer presentations | **Known pattern** |
| Preserve guarded or unguarded recursion through a resumption transformer | coinductive generalized resumptions over a complete Elgot base monad | **Known theorem** |
| Give a row-typed handler calculus with safety | core Eff and later abstract effect-algebra calculi | **Known theorem family** |
| Give domain-theoretic adequacy for a recursive handler calculus | core Eff's domain model and minimal-invariant-relation adequacy | **Known theorem family** |
| Abstract over the representation of effect collections | effect algebras with generic safety conditions | **Known theorem** |
| Prove modular metatheory for extensible syntax and rules | generic/decomposed proofs for extensible languages | **Known broader methodology** |
| Embed the old monad into a coproduct/free extension | injective coproduct embeddings under suitable existence assumptions | **Largely known semantically** |
| Preserve the old *operational rules* on old syntax | immediate from a disjoint conservative syntax extension | **Routine, not novel alone** |
| Transport a named package of old safety, recursive adequacy, observations, morphisms and relations through one extension interface | no exact theorem located in the audited sources | **Candidate gap, not yet confirmed** |
| Recover an exact transformed old base grade from an unordered free-effect row | contradicted by our Writer examples without further interaction data | **Candidate boundary theorem** |
| Characterize when old and new handlers commute or preserve old observations | related to effect combination and distributive-law literature, but our exact certificate-level statement was not located | **Candidate gap requiring a sharper theorem** |

## Why the resumption layer is not a novelty claim

Goncharov, Schröder, Rauch and Jakob start with a monad for base effects and adjoin
free operations using a cofree-coalgebra construction.  Their coinductive generalized
resumption transformer preserves unrestricted iteration when the base is a complete
Elgot monad, and has a universal characterization through coproducts of complete Elgot
monads.  This matches the mathematical centre of our recursive carrier and iteration
argument very closely.

Consequently, the following should be treated as imported theory once the hypotheses
are aligned:

- the recursive resumption carrier;
- its monad structure;
- preservation of complete-Elgot iteration;
- the universal/coproduct reading of adjoining operations.

Our work may still specialize or operationalize this theory, but specialization is not
itself a novelty claim.

Source: [Unguarded Recursion on Coinductive Resumptions](https://arxiv.org/abs/1405.0854),
[Complete Elgot Monads and Coalgebraic Resumptions](https://arxiv.org/abs/1603.02148).

## Why safety and adequacy are not novelty claims alone

Bauer and Pretnar give core Eff an effect system, prove operational safety, construct a
domain-theoretic semantics using minimal invariant relations, and prove adequacy.  The
paper therefore already joins handlers, an effect system, recursion-sensitive domain
semantics and adequacy in one language.

Plotkin and Power's adequacy work also treats call-by-value calculi with algebraic
effects over general algebraic operations, including recursion.  Forster, Kammar,
Lindley and Pretnar establish safety and semantic results for user-defined effects in
several handler calculi.  Thus our Writer/State/Exception adequacy instances are useful
validation and assumption discovery, but not an adequate novelty claim by themselves.

Sources: [An Effect System for Algebraic Effects and Handlers](https://arxiv.org/abs/1306.6316),
[On the Expressive Power of User-Defined Effects](https://arxiv.org/abs/1610.09161).

## Why abstract effect-system safety is not our gap

Yoshioka, Sekiyama and Igarashi parameterize a handler calculus by an abstract
**effect algebra**.  Safety follows once that algebra satisfies explicit safety
conditions; multiple concrete representations of effect collections are instances.
This directly occupies the space of “prove handler safety once for arbitrary effect
rows/sets.”

Our intended abstraction must therefore be different.  It concerns an *already
interpreted base language* carrying more than an outward effect collection:

$$
\mathcal P
=
(\text{syntax},\text{machine},\text{base semantics},\text{recursion},
 \text{observations},\text{proof certificates}).
$$

The extension question is whether a free signature $\Sigma$ maps such a package to a
new certified package $\operatorname{Ext}_\Sigma(\mathcal P)$, and exactly which
parts survive.  Effect-algebra safety covers one component of this package, not the
whole proposed transport theorem.

Source: [Abstracting Effect Systems for Algebraic Effect Handlers](https://arxiv.org/abs/2404.16381).

## Why “modular metatheory” is still too broad a novelty claim

Michaelson, Nadathur and Van Wyk explicitly study host languages extended by
independently developed syntax and semantic rules.  They decompose proofs at language
fragment boundaries and reason generically about unknown extensions, so that proofs
can be composed for a resulting language.  Pyrosome likewise targets extensible
verified compilation.

This makes the slogan “metatheory survives language extension” prior art at the
methodological level.  A defensible result here must exploit the special algebraic
structure of operations and handlers and must state conclusions not supplied by a
generic syntactic-extension framework, for example:

- semantic adequacy relative to a pre-existing effectful model;
- preservation and reflection of a chosen observation map;
- compatibility with complete-Elgot iteration;
- precise interaction obligations for existing handlers;
- counterexamples showing that an unordered row cannot determine a transformed old
  grade.

Source: [A Modular Approach to Metatheoretic Reasoning for Extensible Languages](https://arxiv.org/abs/2312.14374),
[Pyrosome: Verified Compilation for Modular Metatheory](https://arxiv.org/abs/2507.06360).

## The strongest surviving candidate

The most promising formulation is no longer a single monad-construction theorem.  It
is a **certificate-transport theorem with a sharp failure boundary**.

Let a base-language package expose three progressively stronger certificates:

1. $\mathsf{BaseSafety}$: decomposition, preservation, progress and old-syntax
   conservativity;
2. $\mathsf{RecursiveAdequacy}$: a recursive semantic model, iteration/fixpoint
   compatibility and an operational/denotational relation;
3. $\mathsf{Observation}$: a declared ground observation and the conditions under
   which the relation reflects it.

Then adjoining a first-order free signature with exhaustive deep handlers should:

- preserve certificate 1 from local syntactic and row conditions;
- preserve certificate 2 using the known resumption/complete-Elgot construction;
- preserve certificate 3 only when the observation relation and handler clauses meet
  explicit admissibility conditions;
- preserve exact old base grades or old-handler equations only when a separate
  interaction certificate is supplied.

The final bullet is essential.  It prevents the theorem from silently promising more
than unordered may-effect information contains.

## Evidence still required

Before treating the surviving candidate as novel, we must do all of the following:

1. define the input package and certificate morphisms without baking the theorem into
   the definitions;
2. derive each output certificate, identifying which steps are direct applications of
   prior universal properties;
3. instantiate the theorem for Writer, State and Exception;
4. prove a small impossibility result for exact old-grade transformation from rows
   alone;
5. compare the final statement, not just its ingredients, against modular metatheory,
   abstract effect algebras, modular algebraic effects and resumption transformers;
6. ask an expert or reviewer to challenge the “no exact theorem located” cells.

Until those steps are complete, the status is **promising synthesis plus candidate
boundary theorem**, not established novelty.
