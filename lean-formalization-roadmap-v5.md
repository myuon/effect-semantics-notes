# Lean formalization roadmap

## Status

**Implementation plan.** This page identifies which paper claims need kernel
checking, which claims can initially remain on paper, and the order that avoids
committing early to category-theoretic or domain-theoretic infrastructure.

**Implementation in progress.** The [`formal/`](https://github.com/myuon/effect-semantics-notes/tree/main/formal)
Lean project pins Lean 4.32.2. M0--M2 and M3 sharp affine operational
preservation are checked without `sorry`. The concrete Writer layer now checks
free-tree monad laws, source/tree Writer adequacy, structural relation and map
laws, finite TT closure, shallow TT preservation and ordered grade bounds.
The response-type-indexed refinement and typed source/tree adequacy are now
checked, as are typed shallow structural and TT transport. Mechanization also
found a theorem-level boundary: naive first-occurrence replacement is not
monotone under ordered-subsequence weakening. The abstract certificate must
therefore expose a principal-grade restriction, a coarser monotone envelope,
or a richer effect domain rather than assuming this monotonicity.
The monotone downward-closed language repair, concrete certificate extraction,
State/Exception structural instances and finite derived-deep approximants are
also now checked. The remaining recursive milestone is specifically the
source fixpoint/domain limit and admissible TT argument, not the finite
approximant equations.

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
use as the computation pole of the fundamental relation.

If the remaining M3 proof requires changing the syntax or effect transformer, update the research
notes before proceeding to denotation.  If M5 fails while M1–M4 hold, treat it
as an adequacy/observation problem rather than weakening operational safety.
If M6 fails, the object construction may still be valid: the failure concerns
functorial transport and must not be reported as failure of free operations.

## 8. First concrete deliverable

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
