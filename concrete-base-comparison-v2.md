# Concrete base comparison v2

## Status

**First cross-instance extraction after Pure, Writer, State, and Exception.**
This page records what can now be generalized and where a choice remains.

## 1. Completed instances

| Base | Concrete carrier | Additional base outcome | Key interaction |
|---|---|---|---|
| Pure | free request tree | none | baseline handler behavior |
| Writer | normalized Writer-segment tree | accumulated output | clause count and insertion order |
| State | state-to-resumption tree | reached state | current-state threading across resumptions |
| Exception | return/raise/request tree | abort | nesting order of old and new handlers |

Across all four, the new free-effect row and direct handler rules remained
unchanged.

## 2. Common operational interface discovered

The proofs use a base machine that, from a closed active base computation, can
deterministically produce one of:

$$
\mathsf{BaseReturn}(v,\xi'),
$$

$$
\mathsf{BaseStep}(M',\xi'),
$$

or a base-specific terminal/nonreturn outcome

$$
\mathsf{BaseAbort}(o,\xi').
$$

$\xi$ is the base runtime state: trivial, Writer log, State store, or absent for
the simple exception machine.  New free requests are not base outcomes; they
remain syntactically exposed with a captured continuation.

The common operational assumptions used so far are:

1. unique CBV active context;
2. deterministic base transition or outcome;
3. base primitives are silent in the new free row;
4. base steps lift through a pending free handler;
5. a base return is the only base outcome sent to the free handler's return
   clause;
6. base nonreturn outcomes propagate unless an old base construct handles them;
7. nonmatching handlers are retained in forwarded continuations.

These assumptions suffice for free-row preservation, effect-aware progress,
empty-row safety, and dynamic deep elimination in all four instances.

## 3. Common denotational shape discovered

All three nontrivial tree models have the form

$$
\text{run a base layer until it yields either}
\begin{cases}
\text{return},\\
\text{base-specific nonreturn},\\
\text{new free request with continuation}.
\end{cases}
$$

This is captured schematically by a resumption equation

$$
\mathsf{Res}_{T,\Sigma}A
\cong
T\left(A+\Sigma(\mathsf{Res}_{T,\Sigma}A)\right),
$$

or an equivalent free-monad-transformer presentation, provided the chosen $T$
and recursive construction exist.

- Writer normalizes the $T$ layer into a prefix segment.
- State exposes the current state in the observation of the $T$ layer.
- Exception places `Raise` beside the free request alternative.

The new deep handler recurses on the exposed free structure.  It does not
inspect arbitrary opaque values of the original monad without such a
presentation.

## 4. Results that generalized cleanly

The following have now survived all concrete instances at paper level.

- syntax and typing embedding with an orthogonal unordered free row;
- deterministic return/step/base-outcome/free-request decomposition;
- free-row preservation;
- effect-aware progress;
- empty new row excludes unhandled new free requests;
- exhaustive deep handling eliminates its interface from the outward new row;
- old programs embed conservatively into the extended language;
- identity-return free handlers are inert on base-only programs, subject to
  propagation of base-specific outcomes;
- free-tree or resumption denotation validates matching and forwarding;
- operational steps preserve the concrete tree denotation.

## 5. Results that did not generalize from row data

An unordered row does not determine:

- how many times an effectful clause runs;
- where Writer output is inserted;
- how many State transitions are composed;
- whether a clause-generated exception is inside an old `try`;
- how multi-shot resumptions duplicate or sequence future base behavior.

Therefore the row layer is adequate for **effect safety and discharge**, but
not for an exact transformer of arbitrary base effects.

## 6. Two independent extension questions

The concrete studies separate the project into two theorems.

### Safety extension

Can a base language be extended so that new user-defined requests are tracked,
forwarded, and exhaustively discharged without changing old programs?

The evidence is strongly positive under the operational assumptions above.

### Base-effect transformation

Can the old base effect annotation predict the base behavior introduced by
interpreting all new requests?

The answer is negative from unordered row data alone for exact Writer and State
grades, and is scope-sensitive for Exception.  Additional interaction
structure is necessary.

## 7. First revised package boundary

The original [Base semantic package v2](base-semantic-package-v2.md) bundled
many optional fields.  The examples suggest separating:

1. **BaseSafety**: deterministic operational outcome interface, old typing, and
   free-row silence of base primitives;
2. **BaseResumptionModel**: a presentation exposing return, base nonreturn, and
   new free request structure;
3. **BaseObservation**: the observations for adequacy;
4. **HandlerInteraction**: laws governing duplication, discard, and scope of
   base behavior under resumptions;
5. **BaseEffectAbstraction**: a static abstraction of the intensional model,
   with a sound handler transformer if one exists.

This separation is more faithful than requiring every base effect system to be
one opaque graded monad.

## 8. The first point where straight generalization stops

We can now state a common safety-extension theorem candidate, but we cannot yet
state one uniform theorem for the **precise output base grade**.

There are at least three legitimate continuations:

1. prove only the generic safety/conservativity/resumption theorem;
2. add a coarse base-effect closure operation sufficient for sound upper
   bounds;
3. retain an intensional trace/count/tree refinement and abstract it into each
   base effect system.

Choosing among these changes the main theorem.  The examples do not select one
uniquely.  This is the first substantive design fork reached by the concrete
program.

## 9. Recommended next move

Before choosing the fork, formalize the common **safety extension theorem**
using `BaseSafety` and `BaseResumptionModel`, without promising a precise output
base grade.  Then state the grade-transformation problem as an optional second
layer and compare the three solutions above.

This preserves the original motivation: identify exactly how far extension is
automatic, and exactly where old and new effects need an explicit interaction
law.
