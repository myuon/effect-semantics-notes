# State deep-handler study v2

## Status

**Concrete operational instance and paper metatheory.** We use integer state in
examples and an arbitrary state set $S$ in theorem statements.

## 1. State machine

Configurations are

$$
\langle s,M\rangle.
$$

The base primitives are

$$
\operatorname{get}:1\to S,
\qquad
\operatorname{put}:S\to1,
$$

with transitions

$$
\langle s,\operatorname{get}()\rangle
\longrightarrow
\langle s,\operatorname{return}s\rangle,
\tag{S-Get}
$$

$$
\langle s,\operatorname{put}(s')\rangle
\longrightarrow
\langle s',\operatorname{return}()\rangle.
\tag{S-Put}
$$

Both primitives are silent in the new free-effect row.  They are not pure in
the base semantics.

Use the same free interfaces $\mathsf{Ask}$ and $\mathsf{Ping}$ and the same
identity-return deep handlers as in the Writer study.

## 2. Six common calculations

### Conditional request

$$
H_A^{\mathsf{true}}(
\mathbf{if}\ b\ \mathbf{then}\operatorname{ask}()
\ \mathbf{else}\operatorname{return}\mathsf{false})
$$

returns `true` when $b$ is true and `false` otherwise, without changing state.
As in Writer, the outward free row is empty in both executions even though the
operation clause is invoked in only one.

### Forwarding before a matching request

$$
H_P(H_A^{\mathsf{true}}(
\operatorname{ping}();\operatorname{ask}()))
$$

returns `true`.  The outer Ping handler resumes into the pending inner Ask
handler.  State is unchanged.

### Two matching requests

$$
H_A^{\mathsf{true}}(
\operatorname{ask}();\operatorname{ask}())
$$

handles both requests because each matching resumption reinstalls $H_A$.

### State-effectful clause

For integer state define

$$
\begin{aligned}
h_A^{+}=\{&
\operatorname{return}(x)\mapsto\operatorname{return}x;\\
&\operatorname{ask}(u,k)\mapsto
\mathbf{let}\ n\leftarrow\operatorname{get}()\ \mathbf{in}\\
&\qquad\operatorname{put}(n+1);k\,\mathsf{true}
\}.
\end{aligned}
$$

Starting from $n$, zero, one, and two Ask requests finish in states

$$
n,
\qquad
n+1,
\qquad
n+2.
$$

All three inputs may be widened to the same free row $\{\mathsf{Ask}\}$.

### Nested distinct handlers

If the Ping clause increments by $10$ and the Ask clause increments by $1$, then

$$
\operatorname{ping}();\operatorname{ask}()
$$

under either ordinary linear nesting finishes at $n+11$.  This checks
forwarding and original request order, not general commutativity.

### Base-only program under a free handler

$$
H_A^{\mathsf{true}}(
\operatorname{put}(m);\operatorname{get}())
$$

returns $m$ in state $m$.  An identity-return free handler is operationally
inert on this base-only computation.

## 3. A genuinely State-specific calculation

Writer only accumulates output.  State lets a continuation consume and change
the state supplied at resumption.

Define a multi-shot Ask clause schematically by

$$
\operatorname{ask}(u,k)\mapsto
\mathbf{let}\ x\leftarrow k\,\mathsf{true}\ \mathbf{in}\
k\,\mathsf{false}.
$$

Let the captured continuation increment the state once.  Starting from $n$,
the first resumption finishes at $n+1$; evaluation then invokes the second
resumption using that current state, so it finishes at $n+2$.

Thus our direct CBV machine gives **global sequential state across resumptions**.
It does not automatically restore the state captured at the operation site.
A backtracking-state interpretation would require an explicit different
handler or a different composition of State with the free tree.

## 4. Operational decomposition

:::{prf:theorem} State configuration decomposition
:label: thm-state-decomposition-v2

For every closed, well-typed configuration $\langle s,M\rangle$, exactly one
of the following holds:

1. $M=\operatorname{return}V$;
2. there are unique $s',M'$ with
   $\langle s,M\rangle\to\langle s',M'\rangle$;
3. $M$ uniquely exposes a first unhandled free request
   $E^\Delta[\operatorname{op}_{\Delta,i}(V)]$.
:::

:::{prf:proof}
The Writer unique-active-position proof applies unchanged.  Replace the unique
`tell` transition by the two disjoint deterministic primitive forms `get` and
`put`.  A closed, well-typed primitive parameter determines the unique state
transition.  Handler matching and transparent-context forwarding are
independent of the state component.
:::

:::{prf:corollary} State reduction is deterministic
:label: cor-state-determinism-v2

One-step reduction on State configurations is deterministic.
:::

## 5. Free-row safety

:::{prf:theorem} State free-row preservation and progress
:label: thm-state-row-safety-v2

The State instance satisfies:

1. if $\Gamma\vdash M:A!\rho$ and
   $\langle s,M\rangle\to\langle s',M'\rangle$, then
   $\Gamma\vdash M':A!\rho$;
2. a closed well-typed computation either returns, takes a unique step, or
   exposes an unhandled request whose interface belongs to its outward row;
3. an empty-row computation cannot be blocked on a free request.
:::

:::{prf:proof}
The substitution and deep-resumption cases are identical to Writer.  `get` and
`put` replace free-row-silent base primitives by free-row-silent returns.
Progress uses the totality of `get` and `put` for every state and well-typed
parameter.
:::

## 6. Deep elimination and conservativity

:::{prf:theorem} State deep elimination
:label: thm-state-deep-elimination-v2

An exhaustive deep handler with $\Delta$-free outward row prevents every
$\Delta$ request from escaping, independently of the initial and final state.
:::

The proof is the same preservation-plus-progress contradiction as in Writer.

:::{prf:theorem} State language-extension conservativity
:label: thm-state-conservativity-v2

A term using no new free operation or free handler has exactly its old State
transitions and observations, with empty new free row.
:::

An identity-return free handler is additionally inert on a base-only State
term.  Again, this is qualified: a nonidentity return clause may read or modify
state after the base computation returns.

## 7. State-grade precision boundary

Take an exact relational base effect annotation

$$
R\subseteq S\times S.
$$

For integer state, the three zero/one/two-request programs above have the same
input free-row upper bound but handled transition relations

$$
\{(n,n)\},
\qquad
\{(n,n+1)\},
\qquad
\{(n,n+2)\}.
$$

Therefore an unordered row and one clause transition do not determine the
exact handled state transition.  Counts, reflexive-transitive closure, or an
intensional tree are again required for precision.

## 8. Base facts used

| Result | State-specific facts used |
|---|---|
| decomposition/determinism | total deterministic `get` and `put` transitions |
| row preservation | both primitives are free-row silent |
| progress | every well-typed primitive can step in every state |
| deep elimination | no extra State law beyond safety |
| conservativity | State steps lift through free-handler contexts |
| multi-shot observation | resumptions receive the current global state |

Unlike Writer, the denotational model cannot be summarized by prefixing a
monoid output.  It must thread an input state through return, matching clauses,
forwarding, and each resumption.
