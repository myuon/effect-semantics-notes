# Chapter II — direct semantics and concrete free-operation programs

:::{admonition} Lean correspondence — Chapter II
:class: tip
**Lean checked.** Typed requests are represented by [`OperationSignature`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.OperationSignature#doc) and finite request trees by [`FreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc). Concrete Writer conversion and observation are checked in [`GenericBaseInstances`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Examples/GenericBaseInstances.html). [Full mapping](review-guide.md#chapter-ii-free-operations).
:::

## Status

**Operational development.**  This page adds free operations to the
recursion-free Chapter-I calculus.  There are no handlers yet.

## 1. Added syntax and typing

For each interface $\Delta$ and operation

$$
\mathsf{op}_{\Delta,i}:P_i\to R_i,
$$

add the computation

$$
\mathsf{op}_{\Delta,i}(V).
$$

Its typing rule is

$$
\frac{\Gamma\vdash V:P_i}
     {\Gamma\vdash
      \mathsf{op}_{\Delta,i}(V):R_i!\Delta}.
\tag{T-Free}
$$

The source operation receives only $V$.  Its continuation is not source
syntax.  Sequencing remains ordinary `let`.

All Chapter-I rules are reused with effects in

$$
\widehat E=B*\mathcal D^*.
$$

The preorder is compatible with multiplication, extends the base preorder,
and contains $1\leq\Delta$.  Thus a branch that does not perform $\Delta$ may
still be typed at a bound containing it.

## 2. Direct operational semantics

The internal reduction rules and evaluation contexts are unchanged.  Add free
request forms

$$
\mathcal E[\mathsf{op}_{\Delta,i}(V)].
$$

Without a handler, such a form is terminal with respect to the language.  We
write its suspension as

$$
\mathsf{request}_{\Delta,i}
\bigl(V,\lambda r.\mathcal E[\mathsf{return}\,r]\bigr).
$$

This notation belongs to the machine judgment, not the source grammar.  It
merely names the parameter and the evaluation context already present in the
program.

Base requests continue to be processed by the selected Chapter-I machine:

$$
\mathcal E[\beta(V)]
\longrightarrow_B
\mathcal E[\mathsf{return}\,W]
$$

or to a classified terminal base outcome.  Evaluation therefore passes
through base computation until it returns, aborts, or exposes a free request.

## 3. Extended decomposition theorem

The exact four-way statement is Lean checked as
[`HasLanguageComp.progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc),
not merely inferred from the older three-way return/internal/boundary view.

Every closed well-typed Chapter-II computation is uniquely one of:

1. $\mathsf{return}\,V$;
2. an internal redex;
3. an exposed base request $\mathcal E[\beta(V)]$;
4. an exposed free request
   $\mathcal E[\mathsf{op}_{\Delta,i}(V)]$.

The four cases are disjoint because base and free signatures are nominally
disjoint.  The proof extends Chapter-I decomposition with one new syntactic
case.

## 4. Writer plus a free `ask`

Let

$$
\mathsf{ask}:\mathsf{String}\to\mathsf{Bool}
\quad\in\Delta.
$$

Consider

```text
let _ <- tell_a(*) in
let x <- ask("continue?") in
let _ <- tell_b(*) in
return x
```

Its static effect is

$$
[a]\cdot\Delta\cdot[b].
$$

Starting with the empty log, Writer first executes `tell_a`:

$$
\langle M,\epsilon\rangle
\longrightarrow_W^*
\left\langle
\mathbf{let}\ x\leftarrow\mathsf{ask}(\text{"continue?"})\ \mathbf{in}
\mathbf{let}\ \_\leftarrow\mathsf{tell}_b(*)\ \mathbf{in}
\mathsf{return}\,x,
[a]
\right\rangle.
$$

The machine then exposes

$$
\mathsf{request}_{\Delta,\mathsf{ask}}
\left(
\text{"continue?"},
\lambda r.
\mathbf{let}\ \_\leftarrow\mathsf{tell}_b(*)\ \mathbf{in}
\mathsf{return}\,r
\right).
$$

The log is currently $[a]$; $[b]$ is only a possible continuation effect.  If
an external environment supplies `true`, evaluation resumes and finishes with
log $[a,b]$.  If no response is supplied, the request remains exposed and
`tell_b` never runs.

### Optional request branch

```text
let _ <- tell_a(*) in
if c then ask("continue?") else return false
```

The else branch has effect $1$.  Using $1\leq\Delta$, both branches have the
common bound $\Delta$, so the program has $[a]\cdot\Delta$.  When `c=false`,
runtime stops at `return false` without exposing `ask`; this is exactly the may
reading of effects.

## 5. State plus a free `choose`

Let

$$
\mathsf{choose}:\mathsf{Bool}\to\mathsf{Bool}
\quad\in\Delta.
$$

Consider

```text
let old <- get(*) in
let answer <- choose(old) in
let _ <- put(answer) in
return old
```

The bound is

$$
\mathsf{read}\cdot\Delta\cdot\mathsf{write}.
$$

From store `true`, State executes `get` and exposes

$$
\mathsf{request}_{\Delta,\mathsf{choose}}
\left(
\mathsf{true},
\lambda r.
\mathbf{let}\ \_\leftarrow\mathsf{put}(r)\ \mathbf{in}
\mathsf{return}\,\mathsf{true}
\right)
$$

while the store is still `true`.  Responding `false` resumes the continuation,
sets the store to `false`, and returns the old value `true`.  This calculation
checks that the continuation closes over the returned value and runs against
the machine state that exists when it is resumed.

## 6. Exception before and after a free request

Compare

```text
let _ <- raise_boom(*) in
ask("unreachable")
```

and

```text
let x <- ask("reachable") in
raise_boom(*)
```

The first program terminates at `error(boom)` and never exposes `ask`, although
its conservative effect may contain

$$
\mathsf{raise}\cdot\Delta.
$$

The second program first exposes `ask`; only after a response does it terminate
at `error(boom)`.  Its bound is

$$
\Delta\cdot\mathsf{raise}.
$$

Thus the noncommutative annotation distinguishes two possible evaluation
orders without claiming that every annotated effect occurs.

## 7. Operational conclusions

The examples establish the intended boundary:

- base machines run unchanged;
- free operations suspend only when reached;
- source operations do not take continuations;
- the machine recovers a continuation from the unique CBV context;
- static effects conservatively bound possible order and may include effects
  absent from a particular run.
