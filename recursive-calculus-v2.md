# Recursive calculus v2

## Status

**Proposed operational extension of the unordered deep-handler calculus.**
This page fixes the source-level form of general recursion before changing the
denotational model.

## 1. Design decision

Do not add an unrestricted pure constant

$$
\mathsf{fix}_A:(A\to A)\to A.
$$

That would put fixed points in the value category and run directly into the
cartesian-closed/coproduct collapse recorded in [Fixpoint design
constraints](fixpoint-design.md).

Instead add recursive **effectful functions**.  Values and computations gain

$$
V ::= \cdots \mid \mathsf{rec}\ f(x).M,
\qquad
M ::= \cdots \mid V\,W.
$$

The function type exposes a latent computation row:

$$
A\to(B!\rho).
$$

The typing rule is

$$
\frac{
  \Gamma,f:A\to(B!\rho),x:A\vdash M:B!\rho
}{
  \Gamma\vdash\mathsf{rec}\ f(x).M:A\to(B!\rho)
}.
$$

Application has the latent row $\rho$.  The unfolding rule is

$$
(\mathsf{rec}\ f(x).M)\,V
\longrightarrow
M[\mathsf{rec}\ f(x).M/f,V/x].
$$

This keeps recursion in computations: constructing a recursive function is a
value, while unfolding occurs only at an effectful application.

## 2. Why an unordered may-row is stable under recursion

Rows compose by union.  If one unfolding may use interfaces in $\rho$, an
arbitrary finite number of unfoldings still has row

$$
\rho\cup\rho\cup\cdots=\rho.
$$

Thus no new row constructor is required for general recursion.  This is a
benefit of the idempotent may interpretation.  It says only which requests may
appear, not how often or whether execution terminates.

For example,

```text
rec f(x).
  if done(x) then return x
  else let y <- opDelta(x) in f(y)
```

has row $\{\Delta\}$, although it may issue zero, finitely many, or infinitely
many $\Delta$ requests.

## 3. Operational metatheory

The unfolding rule is deterministic and introduces no new terminal form.

:::{prf:theorem} Recursive extended decomposition
:label: thm-recursive-decomposition-v2

Assuming `BaseSafety`, every closed well-typed recursive configuration uniquely:

1. returns;
2. takes one deterministic step;
3. exposes one old base outcome; or
4. exposes one unhandled new request.
:::

The proof is the recursion-free decomposition proof plus the unique application
case.  A recursive application is an unfolding redex after its argument is a
value.

:::{prf:theorem} Recursive row preservation
:label: thm-recursive-row-preservation-v2

The recursive extension preserves value type and unordered free row under each
step.
:::

The only new case is unfolding, proved by simultaneous substitution for $f$
and $x$.

Consequently effect-aware progress, empty-row unhandled-request safety, and
deep discharge remain valid.  Empty-row safety now means

> the computation never gets stuck on a newly added operation.

It does **not** imply termination: `loop = rec f(x). f(x)` has empty row and
steps forever.

## 4. Results deliberately lost

Strong normalization and hereditary head normalization are false.  Therefore
the former proof pattern

```text
normalize to return/request, then compare the root constructor
```

cannot establish adequacy for every closed program.

The following remain meaningful without termination:

- one-step preservation;
- relative determinism;
- finite-prefix safety;
- deep discharge at every reachable state;
- old-language operational conservativity.

## 5. Interaction with the old base grade

The unordered new row needs no iteration operator because union is idempotent.
An arbitrary old base effect algebra may need one.

If one unfolding has old grade $e$, recursive execution may produce

$$
I\sqcup e\sqcup e^2\sqcup\cdots.
$$

A combined effect system must therefore choose one of:

1. an iteration/star $e^*$ in the old base abstraction;
2. a coarse top grade;
3. a recursive grade equation and its least solution;
4. a restriction such as guarded or structurally terminating recursion.

This obligation belongs to `BaseEffectAbstraction`; it is independent of the
sound unordered free-row theorem.

## 6. Quantitative rows

Finite occurrence bounds are generally not closed under unrestricted
recursion.  If a recursive cycle can reach $\Delta$, its sound count is normally

$$
\nu(\Delta)=\infty.
$$

Finite bounds can still be recovered for sized recursion, bounded loops, or a
termination metric.  Count is therefore an optional refinement after the
recursive unordered theorem, not a prerequisite for it.
