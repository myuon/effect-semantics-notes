# Stage 2 operational metatheory v1

## Status

**Completed compositional operational account for the recursion-free Stage 2 core.**

The direct rules in [Shallow matcher calculus v1](shallow-matcher-calculus-v1.md)
correctly describe a single handler around a sequencing context. This page adds
the labelled suspension semantics needed for nested handlers and proves the
resulting decomposition and determinism statements.

## 1. Why direct request forms are not enough

A raw computation can expose

$$
\mathcal E[\operatorname{op}_\Gamma(V)].
$$

But after an inner handler forwards that request, the enclosing term is not
literally a sequencing context around `op`: it may have the form

$$
\mathsf{handle}_\Theta
  (\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta)
\;\mathsf{with}\;H_\Theta.
$$

The inner handler must disappear from the suspended continuation, after which
the outer handler may inspect the same request. This behavior is most clearly
expressed by a labelled suspension carrying a metalevel continuation.

## 2. Responses and resumptions

For any operation

$$
\alpha:P_\alpha\to R_\alpha,
$$

a suspension has the form

$$
M\Uparrow\alpha(V;K),
$$

where

$$
V:P_\alpha,
\qquad
K:R_\alpha\to\mathsf{Comp}(A).
$$

Its meaning is:

> $M$ requests $\alpha(V)$; if the surrounding machine or handler supplies a
> result $W:R_\alpha$, continue as $K(W)$.

The continuation $K$ is metatheoretic. It is not a source value and cannot be
stored, discarded, or invoked twice by a source handler clause.

Base operations $\beta$ and free operations $\operatorname{op}_\Gamma$ use the
same suspension shape but obey different handler-propagation rules below.

## 3. Raw suspension rules

For a sequencing context $\mathcal E$, define

$$
K_\mathcal E(W)=\mathcal E[\mathsf{return}\;W].
$$

Then

$$
\mathcal E[\beta(V)]
\Uparrow
\beta(V;K_\mathcal E),
\tag{S-Base}
$$

and

$$
\mathcal E[\operatorname{op}_\Gamma(V)]
\Uparrow
\operatorname{op}_\Gamma(V;K_\mathcal E).
\tag{S-Free}
$$

These rules package the unique CBV request decomposition. They do not execute
an operation.

## 4. Handler rules over suspensions

Let $H_\Delta(\operatorname{op})$ denote the unique clause
$\operatorname{op}(x)\Rightarrow N$ guaranteed by exhaustiveness.

### 4.1 Matching free request

If

$$
M\Uparrow\operatorname{op}_\Delta(V;K)
$$

and $H_\Delta(\operatorname{op})=\operatorname{op}(x)\Rightarrow N$, then

$$
\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta
\longrightarrow
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;K(r).
\tag{R-Susp-Match}
$$

The handler is absent from both $N[V/x]$ and $K(r)$. This is exactly the direct
matching rule when $K=K_\mathcal E$.

### 4.2 Mismatching free interface

For $\Gamma\neq\Delta$,

$$
\frac{
M\Uparrow\operatorname{op}_\Gamma(V;K)
}{
\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta
\Uparrow\operatorname{op}_\Gamma(V;K)
}.
\tag{S-Handle-Free-Other}
$$

Crucially, the output continuation is $K$, not

$$
\lambda r.\mathsf{handle}_\Delta K(r)\;\mathsf{with}\;H_\Delta.
$$

Thus the inner handler ends, but the suspension remains available for an outer
handler to inspect.

### 4.3 Base request

If

$$
M\Uparrow\beta(V;K),
$$

then

$$
\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta
\Uparrow
\beta\left(V;
  \lambda r.
  \mathsf{handle}_\Delta K(r)\;\mathsf{with}\;H_\Delta
\right).
\tag{S-Handle-Base}
$$

This time the handler **is** retained in the response continuation. A base
operation is part of evaluating the scrutinee toward its first free head; it is
not the free head inspected by the matcher.

This asymmetry is intentional:

$$
\begin{array}{c|c}
\text{suspension} & \text{handler in resumed continuation}\\
\hline
\text{base }\beta & \text{yes}\\
\text{unmatched free }\operatorname{op}_\Gamma & \text{no}
\end{array}
$$

## 5. Return and ordinary internal steps

The return rule remains

$$
\mathsf{handle}_\Delta(\mathsf{return}\;V)\;\mathsf{with}\;H_\Delta
\longrightarrow
\mathsf{return}\;V.
\tag{R-Susp-Return}
$$

If $M\longrightarrow M'$, then

$$
\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta
\longrightarrow
\mathsf{handle}_\Delta M'\;\mathsf{with}\;H_\Delta.
\tag{R-Susp-Ctx}
$$

The premise is an internal step only; a suspension is not an internal step.
Therefore this rule cannot overlap with Sections 4.1--4.3.

## 6. Nested-handler calculations

Let $\mathsf{ask}\in\Gamma$ and $\mathsf{choose}\in\Delta$.

### 6.1 Inner mismatch, outer match

Consider

```text
handle_Gamma
  (handle_Delta
     (let z <- ask_Gamma(*) in return z)
   with H_Delta)
with H_Gamma
```

The raw computation suspends as

$$
\operatorname{op}_{\mathsf{ask}}(*;K).
$$

`S-Handle-Free-Other` removes $H_\Delta$ and propagates the same $(\mathsf{ask},K)$
to $H_\Gamma$. The outer handler then uses `R-Susp-Match`. Consequently the
inner handler is not reintroduced after the outer branch supplies an answer.

### 6.2 Base request before an inner match

For

```text
handle_Delta
  (let u <- tell("a") in choose_Delta(*))
with H_Delta
```

`S-Handle-Base` exposes `tell("a")` with response continuation

```text
fun _ ->
  handle_Delta choose_Delta(*) with H_Delta
```

so the Writer machine's answer resumes under the pending handler. The later
`choose` is therefore handled.

### 6.3 Unmatched free request before a later match

For

```text
handle_Delta
  (let z <- ask_Gamma(*) in choose_Delta(*))
with H_Delta
```

`S-Handle-Free-Other` exposes `ask` with response continuation

```text
fun z -> choose_Delta(*)
```

which contains no $H_\Delta$. The later `choose` remains exposed. This recovers
the intended one-shot example compositionally.

## 7. Unique suspension

### Lemma OS-001 — Functionality of raw suspension

If

$$
M\Uparrow\alpha(V;K_1)
\qquad\text{and}\qquad
M\Uparrow\alpha'(V';K_2),
$$

then the qualified operation and parameter are syntactically equal and
$K_1(W)=K_2(W)$ for every response value $W$.

### Proof

For a raw term, use unique sequencing-context decomposition. For a handled term,
induct outward through `S-Handle-Free-Other` and `S-Handle-Base`. Exhaustive
matching does not produce a suspension, so it cannot introduce a competing
derivation. $\square$

Continuations are compared extensionally because they are metalevel functions.

## 8. Handler decomposition

### Theorem OS-002 — Deterministic one-step decomposition

For a closed, well-typed Stage 2 computation under a fixed deterministic base
machine, exactly one applicable next outcome exists:

1. a returned value;
2. one internal reduction;
3. one base suspension offered to the base machine;
4. one free suspension offered to the surrounding handler/environment.

Moreover, when the outermost construct is a handler:

- return selects `R-Susp-Return`;
- a matching free suspension selects `R-Susp-Match`;
- an other-interface free suspension selects `S-Handle-Free-Other`;
- a base suspension selects `S-Handle-Base`;
- an internal scrutinee step selects `R-Susp-Ctx`.

### Proof

Induction on the computation, using Stage 1 decomposition for non-handler terms
and the induction hypothesis for a handler scrutinee. The five handler cases are
pairwise disjoint by outcome kind and qualified interface equality. Handler
well-formedness gives a unique matching clause. OS-001 gives uniqueness of the
suspension and its continuation. $\square$

### Corollary OS-003 — Relative determinism

Internal evaluation is deterministic. Combined machine evaluation is
deterministic whenever the base machine's response relation is deterministic.

## 9. Type preservation of suspension propagation

Use the residual-context typing developed in
[Residual context typing v1](residual-context-typing-v1.md).

### Matching

If $K$ accepts an $R$ and has tail effect $e$, and the selected clause computes
an $R$ with $e'$, then

$$
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;K(r)
$$

has effect $e'e$.

### Other-interface forwarding

The suspension and $K$ are unchanged, so their operation/result types and
residual effect are unchanged. Only the nonmatching handler frame disappears.

### Base propagation

The base suspension keeps the pending handler in its response continuation.
After the base machine supplies a correctly typed response, the resulting term
is again a well-typed handler configuration. The base operation's contribution
belongs to the accumulated machine trace.

These yield labelled preservation. Same-grade subject reduction for the
combined machine is intentionally not claimed: servicing an observable request
moves its effect from the residual program into the machine trace.

## 10. Operational status and remaining boundary

For the recursion-free core, the following are now fixed:

- source syntax and CBV order;
- raw request decomposition;
- matching, return, other-interface forwarding, and base propagation;
- behavior under nested handlers;
- exactly-once implicit matching resumption;
- non-reinstallation after free matching or forwarding;
- unique decomposition and relative determinism;
- local/labelled type preservation.

The remaining work is not an ambiguity in operational semantics. A fully formal
metatheory would still expand routine induction details and define a concrete
machine configuration carrying accumulated base traces. Recursion can later add
divergence without changing the one-step rules.

We may therefore proceed to denotational semantics, taking the suspension rules
in this page as the operational specification to validate.
