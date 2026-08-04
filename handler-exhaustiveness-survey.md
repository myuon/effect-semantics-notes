# Handler exhaustiveness survey

## Status

**Literature and language-design survey, checked 2026-08-04.**

Question:

> When a user-defined effect interface contains several operations, must a
> handler implement all of them, or may it handle only a subset and forward the
> rest?

There is no universal convention. Existing systems cluster around two coherent
designs, plus several hybrids.

## 1. Executive comparison

| System | Static effect safety | Handler unit | Missing operation clause | Continuation discipline | Relation to our core |
|---|---:|---|---|---|---|
| Koka | yes | effect/handler record | handler representation contains all operations | clause-dependent; resumptions available | close on exhaustiveness, different on continuation power |
| Effekt | yes | interface implementation | handler defines every operation declared by the interface | implicit `resume`, general handler behavior | close on interface exhaustiveness, generally deep/resumptive |
| Frank | yes | interpreter for a statically specified command set | handled command set is explicit in the operator type | commands handled by operator clauses | philosophically close, but its bidirectional/ambient ability system is different |
| OCaml 5 | no effect safety | pattern cases over an open effect GADT | unmatched case returns `None` and forwards outward; top-level miss raises `Effect.Unhandled` | one-shot continuation, dynamically checked | deliberately more permissive and dynamically partial |
| Some formal calculi | varies | complete signature handler | all operation clauses required | often explicit $k$ | exact precedent for our simplifying restriction |

The important distinction is:

> **Exhaustive case analysis** is not the same as **exhaustive effect
> elimination**.

A wildcard makes the runtime matcher total, but if the wildcard forwards a
request then the corresponding effect has not been eliminated.

## 2. Koka: exhaustive handler records

Koka has row-polymorphic effect types and statically discharges handled effect
labels. Its current runtime documentation says that handler types contain all
operations, comparing them to a virtual method table:

- [Koka handler runtime documentation](https://koka-lang.github.io/koka/doc/std_core_hnd.html)
- [Koka language book: effect handlers](https://koka-lang.github.io/koka/doc/book.html#sec-effect-handlers)

This is strongly aligned with our adopted judgment

$$
\Gamma\vdash H:\Delta\Rightarrow e'.
$$

There are nevertheless major differences:

1. Koka uses effect rows with duplicate labels, not our ordered free-product
   words.
2. A Koka clause may abort, resume, or use more general control behavior.
3. Koka has an explicit `mask` operation for skipping an inner handler. Its
   type reintroduces the skipped effect label, preserving the fact that another
   handler is required.

The third point is especially relevant. Koka does not model partial elimination
by silently deleting a label. When an operation deliberately skips an inner
handler, the remaining effect is reflected in the row.

## 3. Effekt: interfaces implemented by handlers

Effekt declares operations together in an `interface`. The official language
tour describes a handler as an interface implementation containing definitions
for each declared operation:

- [Effekt language tour: effects](https://effekt-lang.org/tour/effects)
- [Effects as Capabilities](https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt/)

Handling discharges the interface capability from the computation's required
capabilities. This again supports the interpretation:

> a $\Delta$-handler supplies the meaning of the whole $\Delta$ interface.

Effekt is not operationally identical to our language. Its resumptive clauses
have access to an implicit `resume`, and the standard presentation behaves as a
general algebraic handler rather than our fixed exactly-once shallow result
replacement.

Thus Effekt supports our **exhaustiveness choice**, but not by itself our
**shallowness choice**.

## 4. Frank: handlers as interpreters of command sets

Frank calls effect sets *abilities*. An operator is an interpreter for the
commands specified at its ports, and those command sets are tracked statically:

- [Do Be Do Be Do: The Frank Programming Language](https://arxiv.org/abs/1611.09259)

This is close to our interface-as-theory philosophy: a handler is not merely a
pattern that might recognize something; it is an interpretation for a declared
collection of commands.

Frank differs more substantially in surface and type structure. Handlers are
integrated into operator application, ambient abilities flow inward, and the
language supports multi-handlers. It is therefore evidence for the broad design
principle, not a direct model for our typing rule.

## 5. OCaml 5: intentionally partial and dynamically forwarded

OCaml 5 represents effects as an extensible GADT and handler clauses as pattern
matching. A handler can recognize only selected constructors. In the lower-level
API, returning `None` from the effect case forwards the request to an outer
handler. If no handler accepts it, execution raises `Effect.Unhandled`:

- [OCaml manual: effect handlers](https://ocaml.org/manual/5.5/effects.html)
- [OCaml `Effect` API](https://ocaml.org/manual/5.5/api/Effect.html)

The manual explicitly contrasts OCaml with Eff and Koka: OCaml does not track
effects in types and does not statically guarantee that every performed effect
is handled.

OCaml therefore demonstrates that partial handlers have a straightforward
**dynamic** semantics. It does not solve our static question of how an ordered
effect index should transform when some operations are forwarded.

Its shallow API is also more programmable than our construct. The programmer
uses `continue_with` to choose the next handler for a resumed continuation. In
our core, continuation resumption is implicit, exactly once, and never
reinstalls the current handler.

## 6. Formal calculi often choose exhaustiveness deliberately

A useful explicit precedent is the PEPM 2024 intrinsically typed compiler
calculus. Its authors state that they do not forward unhandled operations and
require one clause for every operation, in order to simplify the language while
studying compilation of first-class continuations:

- [An Intrinsically Typed Compiler for Algebraic Effect Handlers](https://prg.is.titech.ac.jp/papers/pdf/pepm2024-paper.pdf)

That calculus has deep handlers and explicit continuations, so it is not our
calculus. But it confirms that total-signature handlers are a standard and
respectable research baseline rather than an ad hoc restriction.

Classic algebraic semantics gives another conceptual reason. A handler viewed
as a homomorphism from a free algebra is specified by an interpretation of each
operation in the signature:

- [Programming with Algebraic Effects and Handlers](https://arxiv.org/abs/1203.1539)

Forwarding is then obtained by working over a sum of signatures or by giving
unhandled operations a canonical injection into the target algebra. It is extra
structure, not a consequence of the bare algebra interpretation.

## 7. Three meanings of “partial handler”

The literature uses mechanisms that can look similar syntactically but differ
mathematically.

### Dynamic partiality

The handler tests an open runtime operation value. Missing cases propagate
outward. OCaml is the clearest example. Static effect elimination is not
promised.

### Row-polymorphic forwarding

The handler removes a known label while an open row $\rho$ passes through:

$$
\langle\Delta\mid\rho\rangle
\longmapsto
\rho.
$$

This is safe when $\Delta$ denotes the whole handled interface and all its
operations are implemented. It is extensible with respect to **other effects**,
not partial with respect to operations inside $\Delta$.

### Operation-level partiality

The handler implements only a subset $S\subsetneq\operatorname{ops}(\Delta)$.
Then the residual type must retain
$\operatorname{ops}(\Delta)\setminus S$. This requires operation-granular rows,
signature subtraction, trace transformation, or an equivalent construction.

Our rejected simple rule failed only for this third meaning.

## 8. Decision for this research

Adopt the same separation seen in Koka/Effekt-style interface handling:

1. $\Delta$ is an interface/signature, not a single open operation value;
2. $H_\Delta$ implements every operation in $\Delta$;
3. effects from interfaces other than $\Delta$ may remain in an ambient tail;
4. partiality *within* $\Delta$ is deferred;
5. our independent novelty/design choice remains the one-shot shallow,
   exactly-once implicit resumption.

This keeps the main theorem focused:

$$
H_\Delta:
\widehat T_{b\Delta e}A
\longrightarrow
\widehat T_{be'e}A.
$$

It also leaves a clean future extension. Split a signature

$$
\Delta=S\uplus U
$$

and study a partial eliminator that removes $S$ while retaining $U$. That work
should not be smuggled into the present $H_\Delta$.

## 9. Survey conclusion

Our exhaustiveness assumption is well supported by typed effect languages that
treat an effect as an interface or handler record. It is not universal:
OCaml demonstrates a useful dynamically partial alternative, and row-based
systems can forward unrelated effects safely.

The most accurate summary is therefore:

> Exhaustiveness over the selected interface is common and mathematically
> natural; forwarding of other interfaces is also common; partial elimination
> inside one coarse interface requires additional static structure.
