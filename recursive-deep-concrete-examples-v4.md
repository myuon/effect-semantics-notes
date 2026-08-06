# Recursive deep examples: Writer, State and Exception

## Status

**Concrete Chapter II calculations, placed before the general theorem.**
They distinguish finite recursion, divergence, productive old-effect behavior,
nonmatching forwarding and multi-shot resumptions.

Let the new interface `Tick` contain

$$
\mathsf{tick}:1\to1.
$$

## 1. Writer: finite recursive handling

Define

```text
ticks(0)     = return ()
ticks(n + 1) = tick(); tell("a"); ticks(n)
```

and the deep handler

```text
return x   -> return x
tick(_, k) -> tell("h"); k(())
```

For $n=2$, the reduction pattern is

```text
handle ticks(2)
--> tell("h"); handle (tell("a"); ticks(1))
--> tell("h"); tell("a"); handle ticks(1)
--> tell("h"); tell("a"); tell("h"); tell("a"); return ()
```

and therefore

$$
\mathsf{runWriter}(\mathsf{handle}\;\mathsf{ticks}(n))
=([\texttt{h},\texttt{a}]^n,()).
$$

Every recursive resumption is rewrapped, so all `Tick` requests are handled and
the outward new row is empty.

## 2. Writer: productive divergence and observation level

Define

```text
forever() = tick(); tell("a"); forever()
```

The same deep handler generates the infinite Writer pattern

$$
\texttt{h},\texttt{a},\texttt{h},\texttt{a},\ldots
$$

without ever exposing `Tick`.  In the ordinary partial Writer model

$$
T A=(W\times A)_\bot,
$$

there is no final pair, so the denotation is bottom.  This model validates
termination/divergence adequacy but forgets the productive infinite log.  A
Level-3 theorem requires a trace-producing Writer model rather than following
from deep handling itself.

## 3. Writer: multi-shot resumption duplicates the tail

Let `Choose` contain $\mathsf{choose}:1\to\mathsf{Bool}$ and consider

```text
x <- choose();
tell(if x then "t" else "f");
return ()
```

A clause may call its deep resumption twice:

```text
return _ -> return ()
choose(_, k) ->
  k(true);
  k(false);
  return ()
```

Under sequential Writer semantics, the two invocations produce the log

$$
[\texttt{t},\texttt{f}].
$$

Thus type-and-row safety does not imply resource safety or an exact old Writer
grade.  The semantic package must explicitly permit duplication, or the source
type system must restrict $k$ linearly/affinely.

## 4. State: deep handling across recursive calls

Use the same `ticks` program and initial state $s$.  Let the clause be

```text
tick(_, k) ->
  n <- get();
  put(n + 1);
  k(())
```

Then

$$
\mathsf{runState}(\mathsf{handle}\;\mathsf{ticks}(m),s)
= ((),s+m).
$$

The recursive continuation sees the state installed by the previous clause.
For `forever`, every finite prefix increments the state, but there is no final
state.  The ordinary partial State model observes only divergence; a trace of
transient states requires a richer base observation.

## 5. State: multi-shot means sequential, not automatically backtracking

If a State computation is resumed twice, the second resumption normally starts
from the state left by the first.  Deep handling alone does not clone or restore
the store.  A backtracking interpretation must save and restore state in the
clause or use a different State/handler interaction law.

This is a concrete reason why a generic theorem can preserve adequacy relative
to a supplied State semantics but cannot decree one universal meaning for
multi-shot State.

## 6. Exception: aborting a recursive handler

Let old `raise E` be a base outcome.  With

```text
tick(_, k) -> raise Stop
```

the first `tick` in `ticks(n + 1)` raises `Stop` and never invokes the recursive
resumption.  With the identity clause `tick(_,k) -> k(())`, an old exception in
the resumed tail propagates normally.

For the infinite `forever` program, the identity clause produces divergence
with no escaping `Tick`.  Again, empty new row does not imply return.

## 7. Nonmatching forwarding remains deep

Suppose `Ask` occurs before `Tick`:

```text
x <- ask();
tick();
return x
```

A deep `Tick` handler forwards `Ask` with a continuation that still contains
the handler.  If an outer handler responds to `Ask` and resumes, the later
`Tick` is caught.  This is exactly where Chapter II differs from Chapter I's
first-free-boundary matcher, which terminated when it saw `Ask`.

## 8. Concrete conclusions

The examples jointly establish the intended distinctions:

- deep reinstallation, not recursion, enables complete interface discharge;
- recursion makes the number of handled occurrences unbounded;
- empty new row is compatible with divergence;
- partial Writer/State/Exception models observe finite outcomes and bottom but
  not every productive infinite trace;
- multi-shot clauses require an explicit base-effect compatibility decision.
