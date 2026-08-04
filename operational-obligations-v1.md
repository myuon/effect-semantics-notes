# Operational obligations v1

## Status

**Paper-level discharge of OA-1, OA-2, OA-3, and OA-5 for the fixed
recursion-free Stage 2 calculus. OA-4 is isolated as the definition of a
compatible base machine.**

This page turns the operational hypotheses of the Conditional adequacy theorem
into consequences of the adopted syntax and rules.

## 1. Combined outcomes

Use the suspension presentation only as a derived judgement. A closed
computation has one of four outcomes:

$$
\mathsf{Ret}(V),
\qquad
\mathsf{Step}(M'),
\qquad
\mathsf{Base}(\beta,p,K),
\qquad
\mathsf{Free}(\Gamma,\operatorname{op},p,K).
$$

The metalevel continuation has the operation result type:

$$
K:R_\alpha\to\mathsf{Comp}(A).
$$

For a raw sequencing context $\mathcal E$,

$$
K_{\mathcal E}(r)=\mathcal E[\mathsf{return}\;r].
$$

For a base suspension propagated through a handler, the continuation retains
that handler. For an other-interface free suspension, it does not.

## 2. Raw unique decomposition

### Lemma OD-001 — Stage 1 decomposition

Every closed well-typed computation without an outer handler has exactly one
of the four outcomes above.

### Proof

Induction on the computation typing derivation.

- `return` gives $\mathsf{Ret}$.
- A base or free primitive gives the corresponding suspension with identity
  context.
- In `let x <- M in N`, apply the induction hypothesis to $M$. A return gives
  the unique `let-return` step; an internal step lifts uniquely; a suspension
  extends its unique sequencing context by the outer `let`.
- Closed application, conditional, and case use canonical forms. Exactly one
  principal rule applies.
- `T-Sub` changes no term or dynamic outcome.

Uniqueness of the sequencing context follows because its grammar descends only
through the active left premise of `let`. The four outcome constructors are
disjoint. $\square$

This simultaneously extends B-003 from base requests to qualified free
requests.

## 3. Handler decomposition

### Lemma OD-002 — One handler frame

Suppose the scrutinee of

$$
\mathsf{handle}_\Delta M\;\mathsf{with}\;H
$$

has a unique outcome. Then the whole term has a unique outcome or reduct:

| Scrutinee outcome | Unique handler action |
|---|---|
| return | `R-Handle-Return` |
| internal step | `R-Handle-Ctx` |
| base suspension | `S-Handle-Base` |
| free suspension from $\Delta$ | `R-Susp-Match` |
| free suspension from $\Gamma\neq\Delta$ | `S-Handle-Free-Other` |

### Proof

The five rows are disjoint by outcome tag and qualified interface equality.
Handler well-formedness gives exactly one clause for every operation in
$\Delta$. The context rule is restricted to internal steps and therefore
cannot cross a suspension. $\square$

### Theorem OD-003 — OA-1: unique combined decomposition

Every closed well-typed Stage 2 computation has exactly one combined outcome.

### Proof

Induction on the number of outer handler frames, using OD-001 at the raw core
and OD-002 for each frame. Equivalently, this is OS-001 and OS-002 with the
Stage 1 induction made explicit. $\square$

Internal reduction is therefore deterministic. Combined execution is
deterministic relative to the response choice of the base machine and external
free environment.

## 4. Typed suspensions

### Lemma OD-004 — Suspension typing

If a well-typed closed computation exposes

$$
\alpha(p;K),
\qquad
\alpha:P_\alpha\to R_\alpha,
$$

then

$$
p:P_\alpha
$$

and for every $r:R_\alpha$, $K(r)$ is a computation of the original result
type, with the residual effect given by its context derivation.

### Proof

For a raw request, invert the primitive typing rule and apply RC-003 and RC-001.
Propagation through sequencing uses CT-Let. For a base suspension propagated
through a handler, reapply the handler typing rule to the typed response
continuation. Other-interface forwarding removes the frame and leaves the raw
typed continuation unchanged. $\square$

### Corollary OD-005 — OA-2: typed responses

The combined semantics may substitute only a value $r:R_\alpha$ into $K$.
Doing so preserves the computation result type. Thus OA-2 is a consequence of
operation typing and residual-context typing, not an independent semantic
assumption.

## 5. Reducibility with observable requests

Ordinary strong normalization is too weakly phrased for a request calculus: a
request is a legitimate head, and adequacy also inspects every possible typed
response continuation.

Introduce the **hereditary transition** $\longrightarrow_h$. It contains all
internal reductions and, for either kind of suspension, every typed response
step

$$
\alpha(p;K)\longrightarrow_h K(r)
\qquad(r:R_\alpha).
$$

This transition is a proof device: operational behavior still records the
request node before considering its response branches. Define reducibility
simultaneously for closed values and computations.

### Values

- Unit, booleans, primitive values, products, and sums use the standard
  simply-typed reducibility clauses.
- A function value $V:A\to(B!L)$ is reducible if $V\,W$ is reducible for every
  reducible closed $W:A$.

### Computations

A closed $M:A!L$ is reducible when it is strongly normalizing under
$\longrightarrow_h$, and every return reachable from it contains a reducible
value. Quantification over typed response steps makes this hereditary across
every branch without a circular definition of computation reducibility.

### Lemma OD-006 — Closure under internal reduction

If $M\longrightarrow_h M'$ and $M'$ is reducible, then $M$ is reducible,
provided every other immediate successor of $M$ is reducible as well.

For an internal step there is no other successor by OD-003, so the usual
one-step expansion lemma follows. Conversely, every successor of a reducible
$M$ is reducible.

### Lemma OD-007 — Sequencing closure

If $M:A!L$ is reducible and $N[V/x]$ is reducible for every reducible $V:A$,
then

$$
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
$$

is reducible.

### Proof

Argue by well-founded induction over the $\longrightarrow_h$ reduction tree of
$M$.

- At return, take `R-Let-Return` and use the premise for $N[V/x]$.
- At a request, every typed response is an immediate hereditary successor. The
  induction hypothesis applies to the old continuation, after which the premise
  for $N$ gives reducibility of the extended continuation.

Determinism rules out any other internal path. $\square$

## 6. Reducibility of shallow handling

### Lemma OD-008 — Handler closure

Suppose $M$ is reducible and every substituted exhaustive clause
$N_{\operatorname{op}}[p/x]$ is reducible. Then

$$
\mathsf{handle}_\Delta M\;\mathsf{with}\;H
$$

is reducible.

### Proof

Well-founded induction on the $\longrightarrow_h$ reduction tree for $M$.

- At return, one handler-return step reaches a reducible return.
- An internal scrutinee step is handled by OD-006 and the induction hypothesis.
- At a base suspension, the propagated continuation is

  $$
  r\mapsto
  \mathsf{handle}_\Delta K(r)\;\mathsf{with}\;H.
  $$

  Every $K(r)$ is an immediate hereditary successor, so the induction hypothesis
  applies.
- At a matching free suspension, the reduct sequences the reducible substituted
  clause with $K$. OD-007 applies. No handler is reinstalled.
- At another free interface, forwarding exposes the same $K$ without the
  handler. Every response continuation is an immediate hereditary successor of
  $M$ and is therefore reducible.

Exhaustiveness and clause uniqueness ensure that the matching case always has
one well-typed reducible clause. $\square$

The proof uses exactly-once resumption. An unrestricted source-level
continuation variable would require an additional usage-sensitive reducibility
argument.

## 7. Fundamental reducibility

### Theorem OD-009

If $\Gamma\vdash V:A$, then every closing reducible substitution sends $V$ to a
reducible value. If $\Gamma\vdash M:A!L$, it sends $M$ to a reducible
computation.

### Proof

Simultaneous induction on value and computation typing.

- Variables and value constructors are standard.
- Abstraction uses the function reducibility clause and the induction
  hypothesis for its body.
- Application instantiates that clause.
- Return, conditionals, and cases use their corresponding value clauses.
- Sequencing is OD-007.
- Base and free primitives are reducible suspensions: after any typed response
  their identity continuation returns that response.
- A handler uses OD-008 and the induction hypotheses for its scrutinee and all
  clauses.
- Subeffecting changes no dynamics.

$\square$

### Corollary OD-010 — OA-3: hereditary head normalization

Every closed well-typed recursion-free Stage 2 computation reaches a unique
return/base/free head after finitely many internal steps, and every typed
response continuation has the same property. Hence its operational behavior is
a well-founded tree.

## 8. Clause fidelity

Let

$$
c_{\operatorname{op}}(p)
=
\llbracket N_{\operatorname{op}}\rrbracket(\rho,p).
$$

### Lemma OD-011 — OA-5: clause fidelity

Operational substitution of an actual parameter and denotational clause
instantiation agree:

$$
\llbracket N_{\operatorname{op}}[V/x]\rrbracket\rho
=
c_{\operatorname{op}}(\llbracket V\rrbracket\rho).
$$

### Proof

This is semantic computation substitution. The clause-body typing premise from
`T-Handler-WF` supplies its result and effect types. $\square$

Thus OA-5 is derived from substitution; it is not an extra machine property.

## 9. Compatible base machines

OA-4 cannot be proved from source syntax alone because the calculus is
parameterized by an external implementation of base requests. Define a base
machine to be **node-compatible** when:

1. it accepts exactly requests labelled $\beta:P_\beta\to R_\beta$ from the
   fixed base signature;
2. it supplies only typed responses;
3. the behavior record of a request is the node
   $\mathsf{base}_\beta(p,-)$;
4. any additional machine state is accounted for by the chosen base
   observation.

Then OA-4 is clause 3 of this interface definition. Writer is node-compatible:
`tell(s)` records exactly one `tell` node and responds with $*:1$.

This condition does not require the base machine to be deterministic. A
deterministic final-result theorem additionally assumes one response for each
machine configuration; a branching behavior-tree theorem can instead retain
all permitted typed responses.

## 10. Discharge theorem

### Theorem OD-012 — Operational obligations

For the fixed recursion-free Stage 2 calculus:

1. OA-1 follows from OD-003;
2. OA-2 follows from OD-004--OD-005;
3. OA-3 follows from OD-006--OD-010;
4. OA-5 follows from OD-011;
5. OA-4 holds by choosing a node-compatible base machine.

Therefore AD-003--AD-005 require no additional operational hypothesis beyond
the adopted calculus and node-compatible machine interface. Transport to a
chosen model $T$ still requires its base observation adequacy BA.

## 11. Remaining proof boundary

- The reducibility proof is paper-level; formalization must encode hereditary
  suspension continuations and the handler case.
- Primitive value types need their own canonical-form/reducibility clauses.
- Adding `fix` invalidates OD-010 and requires partial or coinductive adequacy.
- Machine state not visible as operation nodes belongs to BA and must not be
  silently discarded.

The genuinely model-dependent remainder is now BA, not the operational
behavior of free operations or shallow handlers.
