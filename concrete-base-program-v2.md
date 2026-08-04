# Concrete base program v2

## Status

**Current development order.** The common free-effect syntax is fixed first;
general abstraction is postponed until several concrete models have been
worked through.

## Methodological decision

We use the direction

$$
\text{common syntax}
\longrightarrow
\text{concrete base instances}
\longrightarrow
\text{instance theorems}
\longrightarrow
\text{common proof pattern}
\longrightarrow
\text{general extension theorem}.
$$

We explicitly avoid beginning with a maximal record of assumptions and then
constructing examples that happen to satisfy it.

## Phase 0: fix only the added language fragment

The following are shared by every instance.

### New operation signatures

An interface $\Delta$ contains finitely many first-order operations

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}.
$$

At source level, an invocation is a computation

$$
\operatorname{op}_{\Delta}(V),
$$

without an explicit continuation argument.  Fine-grain CBV sequencing supplies
the continuation operationally.

### Public free-effect annotation

The new free effects are tracked by an unordered may-row

$$
\rho\in\mathcal P_{\mathrm{fin}}(\mathcal D).
$$

This row tracks which interfaces may escape.  It does not track order, count,
or guaranteed occurrence.

### Handler

The initial handler is:

- exhaustive for one interface $\Delta$;
- deep;
- dynamically catches matching $\Delta$ requests throughout the handled
  computation;
- forwards nonmatching requests while retaining itself in the forwarded
  continuation;
- exposes an explicit resumption that a clause may use zero, one, or many times.

The common syntax is therefore not restricted to linear handlers.  Proofs and
examples are stratified: exactly-once clauses are checked first, affine
exception-like clauses second, and unrestricted multi-shot clauses third.  This
lets us locate the additional base assumptions without changing the language.

### Common observations

For every base, calculate at least these programs:

1. conditional request versus return;
2. a nonmatching request before a matching request;
3. two matching requests in sequence;
4. a handler clause that performs a base effect;
5. nested handlers for distinct interfaces;
6. a base-only program wrapped in a handler.

## Instance P: pure STLC

### Purpose

This is the control instance.  The base effect algebra is trivial:

$$
B=\{I\}.
$$

There is no interaction with old effects, so failures here belong to the new
free-effect calculus itself.

### Expected baseline results

- substitution and weakening;
- preservation and effect-aware progress;
- no unhandled operation at empty row;
- deep elimination of $\Delta$;
- interaction-tree adequacy;
- conservativity over pure STLC.

These are known-style results and are not themselves the novelty target.

## Instance W: Writer base

### Definition

Fix a possibly noncommutative output monoid

$$
(W,\cdot,\epsilon).
$$

The base operation is

$$
\operatorname{tell}(w):1.
$$

The exact operational observation is a value and an output word.  A simple
denotational model is

$$
T A=A\times W,
$$

or its grade-refined form $T_bA$ containing computations bounded by grade $b$.

### Why Writer is first

Writer makes sequencing and duplication directly observable.  If a handler
clause emits $k$, then the position and number of clause invocations can be
read from the final word.

The critical examples distinguish

$$
k\cdot b,
\qquad
b\cdot k,
\qquad
k\cdot b\cdot k.
$$

Thus Writer should expose the first failure of a proposed unordered grade
transformer.

### Instance questions

- Does the free extension preserve exact Writer adequacy?
- Are base-only Writer programs denotationally conservative?
- For base-pure clauses, is the Writer trace unchanged except for control-flow
  effects of resumption?
- For Writer-effectful clauses, what information is needed to bound inserted
  outputs?

## Instance S: State base

### Definition

Fix a set of states $S$ with primitives such as

$$
\operatorname{get}:1\to S,
\qquad
\operatorname{put}:S\to1.
$$

The ordinary denotation is

$$
T A=S\to(A\times S).
$$

For the first pass, the static base effect may be coarse.  A later refinement
can use state-transition relations

$$
R\subseteq S\times S,
$$

composed relationally.

### Why State is distinct from Writer

A base operation returns information that influences the continuation.  This
tests more than accumulation of an output trace.

It also makes resumption behavior visible:

- resuming twice can run the future state computation twice;
- discarding a continuation can discard future updates;
- handler clauses can inspect or modify state around resumption.

### Instance questions

- Does handler folding commute with the state interpretation?
- Which equations require base operations to be algebraic?
- What changes between global state and backtracking state under multi-shot
  resumption?
- Can a relational state grade describe the handler result without trace
  refinement?

## Instance X: Exception base

### Definition

Fix an exception set $X$ with

$$
\operatorname{raise}:X\to0,
\qquad
T A=A+X.
$$

Use a coarse base grade $\{\mathsf{Exn}\}$ initially.

### Why Exception is distinct

Exception aborts the continuation instead of returning a response.  It tests
interaction between an old control effect and the newly added handler scope.

### Instance questions

- If a base exception occurs before a free request, does it escape without
  invoking the new handler?
- If a free handler clause raises a base exception, which handler scope sees
  it?
- Does the order of old exception handling and new free handling change the
  observable result?
- Which conservativity statement survives when the base already has handlers?

## Why these four instances

| Instance | Feature isolated |
|---|---|
| Pure | free calculus with no interaction |
| Writer | noncommutative order and visible duplication |
| State | response-dependent continuation and mutable evolution |
| Exception | abortion and interaction of handler scopes |

Together they prevent a general theorem from being inferred solely from one
friendly algebraic example.

Concurrency, resources, cancellation, continuations, and higher-order scoped
effects are deliberately deferred.  They are important boundary instances but
would obscure the first comparison.

## Per-instance proof protocol

For each base, proceed in the same order.

1. Define source syntax and direct operational semantics.
2. Calculate the six common example programs.
3. Define the denotational carrier and interpretation.
4. Prove or refute base conservativity.
5. Prove or refute preservation and unhandled-effect safety.
6. Prove or refute deep elimination at the unordered row level.
7. Repeat the audit for linear, affine, and unrestricted resumption use.
8. State the strongest operational/denotational correspondence available.
9. Record exactly which base laws the proof used.
10. Add one counterexample obtained by removing a used law.

The first table is now complete at paper level for Pure, Writer, State, and
Exception.  Its extracted common structure and first genuine design fork are
recorded in [Concrete base comparison v2](concrete-base-comparison-v2.md).

## Immediate next task

The shared syntax and operational semantics are now proposed in [Common
free-handler calculus v2](common-free-handler-calculus-v2.md).  The first
operational instantiation and six common calculations are in [Writer deep
handler examples v2](writer-deep-handler-examples-v2.md).

The next task is to audit these definitions for ambiguities and then prove the
Writer instance's decomposition and preservation lemmas before introducing a
denotational model.
