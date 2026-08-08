# Lean formalization roadmap

## Status

**Implementation plan.** This page identifies which paper claims need kernel
checking, which claims can initially remain on paper, and the order that avoids
committing early to category-theoretic or domain-theoretic infrastructure.

**Current checked scope.** The [`formal/`](https://github.com/myuon/effect-semantics-notes/tree/main/formal)
Lean project pins Lean 4.32.2 and contains no `sorry` or project axiom.  M0--M9
are checked for the fixed source calculus.  The finite-boundary part of M10 is
also checked: polymorphic stable-observation ω-CPOs, least fixed points,
admissible poles, open fundamental lemmas, recursive morphism/relation
transport, and Writer/State/Exception instances with adequacy, determinism and
selected-interface discharge.  Operational and finite Writer-denotational
old-language conservativity are proved.

Two scope boundaries are now theorem-level facts rather than missing proof
steps.  First, naive first-occurrence word replacement is not monotone under
ordered-subsequence weakening, so the finite handler theorem uses a principal
grade or monotone language envelope.  Second, no finite ordered word can
absorb a mandatory recursive prefix `[atom]·e ≤ e`; a repetition language can.
Changing the source type system to exploit that repair is a new calculus
choice, not completion of an omitted lemma.

## 1. What the formalization is meant to certify

The first formal artifact should certify the following end-to-end statement
for one fixed, recursion-free Writer calculus:

> adding first-order free operations and the intended partial shallow handler
> preserves typing and ordered effect bounds; the operational handler agrees
> with its free-tree interpretation; closed ground observations are adequate.

This is deliberately narrower than the final categorical theorem.  It checks
the syntax/semantics interface where mistakes are most likely, while producing
definitions that can later be abstracted.

The second target is the transport theorem:

> compatible base morphisms and graded relations lift through the free
> extension, and shallow handling respects the lifted structure.

The recursive/deep theorem is the third target.  It should begin with finite
approximants, not with a general library of domains.

## 2. Classification of claims

### A. Kernel-check before making the main research claim

1. **Core syntax metatheory**
   - weakening and substitution;
   - CBV application effect
     $e_M\cdot e_N\cdot e$;
   - preservation and unique-position progress/decomposition.
2. **Free-operation extension**
   - residual-context plugging;
   - exposed-request decomposition;
   - factorization $p\cdot\Delta\cdot q\le e$;
   - old-language operational conservativity;
   - the no-erasure corollary as a separately assumed result.
3. **Shallow handlers**
   - matching clauses receive a bare continuation;
   - unmatched operations are forwarded with the search handler retained;
   - handler preservation using `forwardGrade`;
   - the partial `tick`/`tock` regression example;
   - exhaustiveness implies interface elimination, but partial handling does
     not.
4. **Concrete Writer denotation and adequacy**
   - the grade-indexed free tree and its bind laws;
   - interpretation of syntax and one-step soundness;
   - operational/structural shallow-handler commutation;
   - return/log/request reflection for closed ground terms.
5. **Structural transport**
   - lifting of a compatible base morphism;
   - identity, composition and monad-morphism laws;
   - graded structural relation, bind closure and graph lemma.

These items jointly test the central recursion-free structure-preservation
claim.  Omitting any whole group would leave one of syntax, denotation,
adequacy or transport unchecked.

### B. Formalize after the recursion-free chain closes

1. the abstract `BaseSafetyCert`, `CarrierCert`, `MonadExtCert`, `FunctorCert`,
   `RelCert`, `FiniteTTCert` and shallow certificate records;
2. the general indexed initial-algebra/free-carrier construction;
3. TT-lifting and the finite fundamental lemma;
4. State and Exception instances as independence checks;
5. recursive operational safety and finite deep approximants;
6. the source-derived deep equations and the exhaustive elimination invariant.

### C. Keep on paper until a concrete need appears

- arbitrary-category packaging of the construction;
- universe-polymorphic functor categories and categorical initial algebras;
- productive infinite-trace adequacy;
- Random with recursive subprobability valuations;
- full abstraction, exact multiplicities and unrestricted multi-shot resource
  reasoning.

These are valuable generalizations, but none is needed to detect an error in
the current core theorem.

## 3. Representation choices

Use an extrinsically typed raw syntax with de Bruijn variables.  Typing remains
an inductive proposition, so preservation is a real theorem rather than a
consequence hidden inside an intrinsically typed datatype.  Define renaming
and simultaneous substitution once and prove their laws before operational
semantics.

Represent an operation declaration by parameter and result types.  Source
syntax contains an ordinary operation expression; it does **not** take a
continuation.  The continuation appears only when a CBV evaluation context
exposes a request:

$$
E[\mathsf{op}(V)]
\quad\leadsto\quad
\mathsf{request}(\mathsf{op},V,\lambda x.E[x]).
$$

Use lists of effect atoms for exact ordered words and a typeclass/record for
the preorder and coherent weakening.  Do not quotient words initially:
proof-relevant derivations make factorization and no-erasure lemmas easier to
state and debug.

Use inductive free trees for the recursion-free denotation.  Define the Writer
instance directly; only after its laws are checked should the common fields be
extracted into abstract structures.  This avoids encoding the paper's
assumptions as Lean axioms and then “proving” the theorem by projection.

## 4. Milestones and theorem inventory

| milestone | Lean results that close it | depends on |
|---|---|---|
| M0 — effects and signatures | word monoid laws; preorder reflexivity/transitivity; weakening coherence; operation lookup uniqueness | none |
| M1 — base calculus | `rename_typing`, `subst_typing`, `step_preservation`, `unique_decomposition`, recursion-free normalization for Writer | M0 |
| M2 — free operations | `request_decomposition`, `request_grade_factor`, `base_conservative`, `empty_free_safe` | M1 |
| M3 — direct shallow handler | `handle_preservation`, `forward_retains_handler`, `matching_continuation_is_bare`, `partial_not_eliminating`, `exhaustive_eliminates` | M2 |
| M4 — Writer free trees | graded `pure`/`bind` laws; weakening laws; semantic substitution; one-step soundness | M1–M3 |
| M5 — finite adequacy | behavior-tree correspondence; handler commutation; ground return/log/request reflection | M4 |
| M6 — morphisms and relations | lifted map identity/composition; monad-morphism laws; structural relation bind; graph lemma | M4 |
| M7 — certificate extraction | concrete Writer proofs instantiate the finite certificate records without extra axioms | M1–M6 |
| M8 — second base models | State and Exception instantiate M1–M7; shared proofs are refactored, model-specific proofs remain local | M7 |
| M9 — recursion/deep control | recursive one-step safety; finite approximant equations; partial-deep regression; exhaustive finite-prefix elimination | M3, M7 |
| M10 — recursive adequacy | chosen pointed-domain model; admissible TT relation; fixed-point fundamental lemma; declared-level reflection | M5, M9 |

M0–M3 are the first executable specification checkpoint.  M4–M7 are the
minimum publishable mechanized result for the present recursion-free theorem.
M9 can start before M8, but M10 should not: a second concrete model is a useful
test that the abstract interfaces have not accidentally encoded Writer.

## 5. Suggested Lean source layout

```text
EffectSemantics/
  Syntax/
    Type.lean
    Effect.lean
    Signature.lean
    Term.lean
    RenameSubst.lean
    Typing.lean
  Operational/
    Context.lean
    Step.lean
    Boundary.lean
    FreeRequest.lean
    ShallowHandler.lean
  Model/
    GradedMonad.lean
    Writer.lean
    FreeTree.lean
    Interpretation.lean
    StructuralHandler.lean
  Metatheory/
    BaseSafety.lean
    FreeSafety.lean
    HandlerSafety.lean
    WriterAdequacy.lean
    MorphismLift.lean
    RelationLift.lean
  Certificate/
    Base.lean
    Free.lean
    Shallow.lean
  Recursive/
    Syntax.lean
    Approximant.lean
    DerivedDeep.lean
    Elimination.lean
    DomainAdequacy.lean
```

Each paper theorem should link to one public Lean declaration.  Helper lemmas
may be internal, but certificate fields should not be populated by `axiom`,
`sorry` or an opaque assumption that restates the desired conclusion.

## 6. Proof order inside the first implementation slice

The first slice should stop at M3 and use only Writer as the base effect:

1. define types, ordered words and the two-operation test signature;
2. define raw terms, values, contexts, plugging and CBV stepping;
3. implement renaming/substitution and prove typing substitution;
4. prove context plugging and request factorization;
5. define partial shallow handling exactly as the operational rules state;
6. prove preservation for return, matching, cross-interface forwarding and
   same-interface partial forwarding separately;
7. encode the `tick`/`tock` example and prove by reduction that `tick` is caught
   while `tock` escapes with the handler in its continuation;
8. prove exhaustive elimination as a different theorem.

This slice resolves the largest remaining semantic-design risk before any
abstract denotational infrastructure is introduced.

## 7. Go/no-go checks

At the end of each milestone:

- no `sorry`, undeclared axioms or theorem-shaped structure fields;
- all examples reduce with `#reduce`/proved evaluation lemmas;
- theorem assumptions match the certificate dependency table;
- negative claims have an explicit typed counterexample;
- CI runs `lake build` from a clean checkout.

M3 operational preservation is now checked: affine response handlers are represented as
separate runtime states, with bare-continuation matching and transparent
forwarding. Partial lookup, exhaustiveness, clause instantiation and the
`tick`/`tock` distinction are mechanized. Principal residual contexts and
ordered first-interface cancellation yield the sharp transformer
`b·Δ·e ↦ b·e'·e`, including typed forwarding/resumption.

M4, M6, M7 and the finite part of M8–M9 are also checked.  For M5, typed
source/tree production, Writer observations and their adequacy equivalence are
checked.  The relation now transports across alternative typing derivations
and effect weakening, and the captured-continuation equation
`openResume.subst0 response = resume response` is proved.  The remaining M5
step is the full source-handler/tree-handler commutation theorem.

The proof-irrelevant operational core of that final M5 step is now checked:
source `let` production is tree `bind`, syntactic and semantic clause tables
are related by an explicit `ModelsWriterHandler` record, and direct shallow
evaluation produces exactly `WriterTree.shallow` in all matching and
forwarding cases.  What remains is its response-type-indexed refinement.

That response-type-indexed refinement is now checked as well.  Typed request
rules expose signature lookup, parameter typing, resume typing and the grade
bound explicitly; typed `let` is typed tree `bind`; and
`ModelsTypedWriterHandler` yields the full typed source/tree shallow
commutation theorem.  Thus finite M5 is complete.  The next genuinely new
semantic obligation is M10 rather than another finite Writer lemma.

The operational half of M9 is now integrated into the same calculus:
recursive-function values bind both an argument and `self`, application uses
checked simultaneous substitution, and preservation/progress cover the new
unfolding rule.  A closed term at the empty effect word reduces to itself
forever, formally separating empty-effect safety from termination.  M10 still
requires a partial/continuous semantic carrier and a fixed-point adequacy
argument.

The first M10 approximation layer is now checked.  Executable head
classification agrees with every internal step and reconstructed base/free
boundary used by the proof; observations are stable under increasing fuel;
and stable observation sequences form a pointed approximation preorder.  The
Writer-specific observer consumes `tell`, accumulates logs, maps every finite
direct Writer run/tree observation to some finite projection, and maps the
silent loop to bottom.  The missing step is the converse reflection theorem
for arbitrary typed observations and its completion into an ω-CPO/fixed-point
model.

The observation carrier is now completed one step further: increasing
ω-chains have a constructed least upper bound, and an explicitly
ω-continuous endofunction has a Kleene least fixed point satisfying both the
unfold equation and least-prefixed-point induction.  Finite Writer return/log
adequacy is now bidirectional.  M10 is no longer blocked on generic fixed-point
infrastructure; what remains is to give the recursive Writer/free-handler
semantic functional, prove its continuity, and connect its fixed point to
typed source recursion and derived deep handling.

The first concrete recursive-handler functional is now checked for Writer.
Finite shallow reinstallation is definitionally the iteration of a monotone
one-layer functional; its operational run relation and fuel observations are
adequate in both directions.  The union of all finite observations satisfies
the concrete deep-handler unfold equation, and the silent recursive loop has
no finite observation.  The remaining M10 obligations are type/effect
indexing of this limit, ω-continuity in the generic carrier, and the
admissible logical-relation/fundamental-lemma layer.

The whole-program approximation space now has its own pointwise ω-chain
completion.  The deep Writer functional preserves every such supremum, its
Kleene chain has exactly the previously defined operational limit as supremum,
and this limit is least among all pre-fixed (hence all fixed) points.  Thus the
generic continuity obligation is discharged for the concrete Writer/deep
handler instance; only its typed effect-indexed and logical-relation
interfaces remain.

The admissibility interface above that CPO is now formal too.  Any predicate
on whole-program approximations that contains bottom, is closed under one
handler layer, and is admissible for pointwise chain suprema holds of the deep
handler limit.  In particular, the lifting that requires every finite result
to satisfy a chosen observation pole is automatically admissible.  Taking the
pole to be the direct operational `DeepWriterRuns` relation rederives limit
soundness by fixed-point induction.  The remaining relation work is no longer
domain infrastructure: it is the type-indexed value/computation fundamental
lemma and its effect-discharge premises.

The first type-indexed endpoint is also checked.  Under a typed affine handler
and the minimal Writer signature law that operation zero returns unit, every
finite result of the recursive deep limit is inhabited by a closed value of
the original computation's result type.  The proof deliberately generalizes
over intermediate effect bounds: clause installation changes those bounds,
but not the result type.  Exact recursive grade transformation is therefore
not smuggled into type preservation.  A richer boundary carrier is still
needed to express that nonselected requests escape while selected requests do
not.

The outward-boundary carrier is now present.  It distinguishes finite return,
old base request and free request boundaries while retaining the Writer log.
Nonselected requests are observable rather than collapsed to bottom.  For a
typed computation and a typed exhaustive handler, every observed outward free
request is proved to have an interface different from the selected one.  This
is the first mechanized semantic discharge theorem for the recursive model;
the next refinement is stability/ω-completion of this richer carrier and its
use as the computation pole of the fundamental relation.  Its finite observer
is now also proved stable under increasing fuel and packaged as a stable
partial observation; only the generic ω-completion remains.

That completion is now generic rather than Writer-specific.  For every
outcome type, stable fuel observations form a pointed antisymmetric
approximation order with constructed ω-suprema; ω-continuous endofunctions
have a Kleene least fixed point with unfold and leastness laws.  The outward
Writer boundary is an instance.  Its limit returns an outcome exactly when
some finite projection does, and selected-interface discharge therefore holds
at the limit as well as at each finite fuel.  This removes the last domain
infrastructure obstacle before the type-indexed computation relation.

The type-indexed relation is now checked.  Values are related by closed value
typing; return, base-request and free-request boundaries are related by the
original result type with existential intermediate effect bounds.  The
resulting computation pole is admissible, every closed typed computation
satisfies it, and the theorem extends to open terms under every typed closing
substitution.  Because recursive values and simultaneous self/argument
substitution are already part of the syntax metatheory, the open fundamental
theorem includes the recursive-function case rather than assuming it.  For
exhaustive handlers it returns boundary typing and selected-interface
discharge together.

Recursive morphism and relation transport are now available independently of
Writer.  A map on finite outcomes that commutes with one semantic unfolding
commutes with the corresponding Kleene least fixed points.  Likewise, any
binary admissible relation containing the two bottoms and preserved by one
unfolding relates the two fixed points.  These are exactly the recursion cases
needed by the paper's morphism-lifting and logical-relation-lifting diagrams;
future instances need prove only their one-layer compatibility premises.

Recursive outward-boundary adequacy is now bidirectional.  A direct inductive
run relation contains separate constructors for return, internal CBV steps,
Writer output, a selected match, an old-base boundary, a different-interface
boundary and a missing selected clause.  It is equivalent both to existence
of a finite fuel observation and to the completed boundary limit.  Thus the
fundamental relation's observation target is independently characterized by
operational runs rather than only by its evaluator.

The generic outcome completion has now been exercised by a second recursive
base.  In the Exception instance, base operation zero is abortive `raise` and
never resumes; return, raise, residual base and residual free boundaries are
distinct.  Direct runs and the stable limit are bidirectionally adequate and
deterministic, while typed exhaustive handlers again prevent the selected
interface from escaping.  This validates that Writer's log threading was not
secretly required by the recursive completion or discharge argument.

The recursive Boolean-State instance is now checked too.  `get` resumes with
the current Boolean state, `put` changes the state for the remainder of the
run, matching free clauses retain the current state, and residual base/free
boundaries record it.  Stable-limit observations and direct operational runs
are bidirectionally adequate and deterministic.  Under the minimal signature
laws that `get` returns Bool and `put` returns Unit, typed exhaustive handlers
discharge their selected interface.  Writer, State and Exception now share
the same generic completion while retaining genuinely different base
interaction laws.

Those three instances are now packaged by a single minimal
`RecursiveBoundaryCert`.  Its fields are exactly a fuel observer, stability,
a direct run relation and finite adequacy.  The completed limit, limit
adequacy, uniqueness of operational outcomes and the equivalence between
bottom and absence of every finite boundary are derived generically.  Writer,
Exception and State instantiate the record and their previously constructed
limits are proved to coincide with the generic one.  This replaces the
paper-level `RecursiveBaseAdequacy` black box for the finite-boundary layer by
an explicit checked interface.

The optional discharge and transport layers are now records as well.
`RecursiveDischargeCert` adds a good-term predicate and a free-interface
projection; the three bases instantiate it from source typing, handler typing,
exhaustiveness and only their own response laws.  `RecursiveMorphismCert`
lists source/target continuity and one-layer commutation.  Its relational
counterpart lists both continuities, binary admissibility, bottom relatedness
and one-layer preservation.  Fixed-point morphism/relation lifting is derived
from these fields, so no conclusion is stored back as a certificate premise.

The graph/morphism coherence question is now checked.  Outcome mapping obeys
identity and composition and preserves chain suprema.  Its graph is a binary
admissible relation.  Every `RecursiveMorphismCert` therefore constructs a
`RecursiveRelationCert` for that graph, whose fixed-point lifting is exactly
the morphism fixed-point equation.  Morphism and graph-relation transport are
not two unrelated assumptions in the recursive layer.

There is now a nonidentity concrete transport instance.  Mapping a Writer
outcome `(log,value)` to `value` commutes with one recursive handler unfolding:
the target functional performs the same control traversal while forgetting
`tell` output.  The equation lifts to every finite approximant and to the
completed fixed point, which satisfies the result-only unfold equation.  This
checks that the transport interface is usable beyond identity maps.

The type-indexed fundamental layer is now replicated for State and Exception,
not just operationally packaged.  Exception boundaries type return, residual
requests and the raised error value; State boundaries type returns and
residual requests while the response laws justify `get`/`put` resumptions.
Their finite-observation poles are admissible, and both closed and open
fundamental theorems hold under every typed closing substitution.  Thus all
three concrete bases cover recursive source substitution, boundary typing,
finite adequacy and selected-interface discharge.

The operational old-language conservativity item from M2 is now explicit as
well.  A mutual `BaseOnly` predicate excludes free-operation syntax from
values, lambda/fixpoint bodies and computations.  It is preserved by renaming,
arbitrary simultaneous substitution, single substitution, recursive
self/argument substitution, every internal step and finite multistep
evaluation.  Consequently no finite reduction sequence starting from an old
term can expose a newly added free request, including after recursive
unfolding.

The denotational half of old-language conservativity is checked too.  Every
finite Writer behavior tree produced by a `BaseOnly` source is itself free of
user-defined request nodes.  Structural shallow handling is the identity on
such trees for every selected interface and handler table.  Hence the old
source behavior and its denotation are unchanged, rather than merely unable
to get stuck at a new operational boundary.

The finite-word grade issue is now a proved boundary rather than an informal
warning.  No finite ordered word `e` can satisfy `[atom]·e ≤ e`, by the strict
length increase of the no-erasure subword preorder.  Thus an unrestricted
recursive body `op; self()` cannot close at a finite latent word.  Conversely,
the downward-closed language of all finite repetitions `atom*` contains the
pure trace and satisfies `[atom]·atom* ≤ atom*`.  Iteration closure is therefore
a sufficient repair for this minimal recursive pattern, while exact finite
words are formally ruled out.

The conservative regular-grade repair is now checked as a separate layer.
For every language `L`, finite powers construct `L*`; Lean proves pure
inclusion, one-unfolding closure, monotonicity, and leastness among all grades
with those properties.  Principal-language embedding preserves pure and
sequential composition and both preserves and reflects finite-word
subeffecting.  An explicit recursive effect-skeleton judgment then derives a
regular grade for every self-free prefix followed by a self call, while also
reusing the finite impossibility theorem to reject every principal finite
annotation for the one-operation loop (`C-360`--`C-362`).

The restriction to one tail-position self call has also been removed at the
grade level.  Effect languages now have empty and binary-union constructions,
and the intersection of all pre-fixed points supplies a Knaster--Tarski least
fixed point for every monotone language functional.  Recursive effect
expressions with pure, atoms, sequence, choice and `self` are positive in the
self grade, so `1 ∪ grade(body,-)` has a canonical least fixed point.  Lean
checks its unfold equation, pure inclusion, body absorption and leastness,
including examples with optional recursion and two self calls in one branch.
For the one-operation loop the generic solution is equal, not merely bounded
by, the explicit Kleene star (`C-363`--`C-365`).

The repair is now connected to an actual source language rather than only an
effect skeleton.  A separate fine-grain CBV calculus carries effect languages
on arrows and computations, uses language union for conditional/case effects,
and includes effectful recursive functions.  Renaming, simultaneous
substitution, recursive argument/self substitution, every internal CBV step,
preservation and closed progress are checked.  A closed `freeOp; self()`
program typechecks at the regular grade and retains it after `fixBeta`; a
conditional recursive variant typechecks by branch union (`C-366`--`C-368`).

## 8. Current formalization boundary

The fixed calculus is now formalized through the strongest claim its present
effect annotations can state:

- recursion-free ordered-word safety, shallow commutation, TT transport and
  finite adequacy;
- recursive operational safety and pure divergence;
- recursive Writer/State/Exception finite-boundary models, least-fixed-point
  infrastructure, adequacy, open fundamental relations and deep discharge;
- generic recursive certificates and fixed-point morphism/relation transport;
- operational and finite Writer-denotational old-language conservativity.

Further work separates into genuine extensions that are not definitionally
determined by the current calculus:

1. **Full effectful recursion syntax.**  The conservative language-valued
   regular closure, old-grade embedding, and general least solution for
   branching/multiple-self effect equations are now fixed.  Source arrows,
   contexts, substitutions, recursion, preservation and progress have been
   reindexed in a conservative parallel calculus.  Typed request
   decomposition, shallow-handler residual grading and the handler
   preservation theorem remain to be transported to language grades.
2. **Productive infinite observations.**  Replace the partial finite-boundary
   model by coinductive traces if infinite Writer output or transient State
   behavior must be observable.
3. **Arbitrary-category packaging.**  Select a category/domain library and
   formalize indexed initial algebras or bilimits.  The current theorems are
   concrete `Type`/finite-observation results and explicit certificate
   transport, not a universe-polymorphic categorical construction.
4. **Random.**  Choose a subprobability/valuation model before recursion; the
   deterministic flat-boundary certificate intentionally does not claim this
   instance.

Items 1--4 require additional semantic or language-design input.  They must
not be silently introduced as assumptions of the theorem already checked.

## 9. First concrete deliverable

The recommended first pull request is **M0–M2**, not the whole roadmap.  Its
acceptance criterion is:

$$
\text{typed closed term}
\Longrightarrow
\text{return, base step, free request, or one unique internal step},
$$

together with preservation, request-grade factorization and base
conservativity.  The second pull request adds M3 and the partial-handler
counterexample.  This boundary keeps reviews small while fixing the calculus
before semantic code depends on it.
