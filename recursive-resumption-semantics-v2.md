# Recursive resumption semantics v2

## Status

**Candidate main semantic replacement after adding general recursion.**  The
finite initial-algebra construction is retained as the terminating fragment,
but no longer suffices for the whole language.

## 1. Why the old carrier fails

The recursion-free carrier was

$$
\mu X.\,T(A+\Sigma_\rho X).
$$

It contains well-founded resumptions and supports structural induction.  A
silent loop such as

```text
rec f(x). f(x)
```

has no finite tree.  Merely replacing $\mu$ by

$$
\nu X.\,(A+\Sigma_\rho X)
$$

does not solve the Pure case either: when $\Sigma_\rho=0$, the right side is
constant $A$ and has no point representing silent divergence.

General recursion therefore needs an explicit semantic home for partiality or
internal delay.

## 2. Recommended abstract input

Replace the plain base monad $T$ by a base computation monad $T_\bot$ equipped
with a coherent iteration operator

$$
f:X\to T_\bot(Y+X)
\quad\mapsto\quad
f^\dagger:X\to T_\bot Y.
$$

The operator satisfies unfolding, naturality, codiagonal/dinaturality, and
uniformity.  This is the structure usually called a **complete Elgot monad**.
It places unguarded recursion in the computation category rather than the value
CCC.

The recursive free extension is the generalized coalgebraic resumption

$$
\mathsf{CRes}_{T_\bot,\rho}A
=
\nu X.\,T_\bot(A+\Sigma_\rho X).
$$

The coalgebra exposes a possibly non-well-founded sequence of base phases and
free requests.  Unguarded recursion is supplied by the iteration structure of
$T_\bot$.  Coalgebraic resumption transformers over complete Elgot monads are a
standard way to combine free effects with iteration; see [Unguarded Recursion
on Coinductive Resumptions](https://lmcs.episciences.org/4784) and [Complete
Elgot Monads and Coalgebraic Resumptions](https://arxiv.org/abs/1603.02148).

## 3. An explicit-delay alternative

For operationally visible internal steps, use interaction trees

$$
\mathsf{ITree}_\rho A
\cong
A
+\mathsf{Tau}(\mathsf{ITree}_\rho A)
+\Sigma_\rho(\mathsf{ITree}_\rho A).
$$

Then

$$
\mathsf{diverge}=\mathsf{Tau}(\mathsf{Tau}(\cdots)).
$$

Reasoning is normally modulo weak bisimulation, which identifies finite
stuttering by `Tau` while retaining divergence.  Interaction trees were
developed precisely as a coinductive free-monad-like representation of
recursive impure programs and compositional handlers; see [Interaction Trees:
Representing Recursive and Impure Programs in
Coq](https://arxiv.org/abs/1906.00046).

For this project the two presentations have different roles:

- complete Elgot/coinductive resumption: abstract main theorem over an existing
  recursive base effect;
- explicit `Tau` trees: operational reference model and a likely future
  mechanization target.

## 4. Concrete base instances

For observations that distinguish return, base outcome, and divergence but do
not retain every intermediate base step, use the following partial models.

### Pure

$$
T_\bot A=A_\bot.
$$

The new bottom point interprets silent divergence.

### Writer

$$
T_\bot A=(W\times A)_\bot.
$$

This distinguishes terminating `(log,value)` from divergence.  It does not
record an infinite stream of outputs produced before divergence.  Exact
productive Writer traces require a coinductive visible-`tell` machine/tree
instead of the normalized big-step Writer monad.

### State

$$
T_\bot A=S\to(A\times S)_\bot.
$$

This gives partial global sequential State.  It observes termination and final
state, but not every transient state of a divergent execution.

### Exception

$$
T_\bot A=(A+E)_\bot.
$$

Return, exception, and divergence are distinct.

These standard partial models are pointed and support least-fixed-point
iteration under the usual continuity assumptions.  Thus all four concrete
examples admit a recursive version.  The observation becomes coarser for
diverging Writer and State computations unless their base actions are made
visible coinductive events.

## 5. Deep handlers

Initiality previously gave a structurally recursive fold.  On
$\mathsf{CRes}$, a deep handler is instead an iterative/coinductive
interpretation.

A matching request may be eliminated without immediately emitting an output
constructor.  Hence naive corecursion can be unguarded.  There are two sound
solutions:

1. interpret the handler using the target complete Elgot iteration operator;
2. in an explicit-delay model, emit a `Tau` for the handler reduction and use
   guarded corecursion.

The second mirrors the small-step rule directly:

$$
\mathsf{handle}(\mathsf{Vis}_\Delta(p,k))
=
\mathsf{Tau}
\bigl(\llbracket c_\Delta\rrbracket(p,
\lambda r.\mathsf{handle}(k(r)))\bigr).
$$

Modulo weak bisimulation, the added finite `Tau` is observationally silent.

:::{prf:conjecture} Recursive deep-handler interpretation
:label: conj-recursive-deep-handler-v2

If the target computation monad has coherent Elgot iteration, the clauses
denote iteration-compatible maps with $\Delta$-free target row, and the target
resumption coalgebra exists, the exhaustive deep handler extends according to
the selected iteration theory/weak bisimulation and discharges the handled
interface from all finite observations.
:::

No bare uniqueness claim is made here: this is not the same proof principle as
the well-founded initial fold, and uniqueness depends on the chosen guardedness
or iteration axioms.

## 6. Finite fragment compatibility

There is a canonical inclusion

$$
\mu X.\,T(A+\Sigma_\rho X)
\longrightarrow
\nu X.\,T_\bot(A+\Sigma_\rho X)
$$

when the base embedding $T\to T_\bot$ is given.  On recursion-free programs,
the recursive denotation must agree with the former finite denotation through
this inclusion.  This is the semantic conservativity obligation for the model
change.
