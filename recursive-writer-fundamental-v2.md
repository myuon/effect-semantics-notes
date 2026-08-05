# Recursive Writer fundamental lemma v2

## Status

**Paper proof of the fundamental logical-relations theorem, including general
recursion and deep handlers.**

## 1. Statement

:::{prf:theorem} Recursive Writer fundamental lemma
:label: thm-recursive-writer-fundamental-v2

If $\gamma\mathcal G_\Gamma\eta$, then:

1. from $\Gamma\vdash V:A$,

   $$
   V[\gamma]\mathcal V_A\llbracket V\rrbracket\eta;
   $$

2. from $\Gamma\vdash M:A!\rho$,

   $$
   M[\gamma]\mathcal C_A^\rho\llbracket M\rrbracket\eta.
   $$
:::

The proof is simultaneous induction on typing, with admissible fixed-point
induction in the recursive-function and handler cases.

## 2. Ordinary value cases

Variables use the environment relation.  Unit, booleans, primitive constants,
pairs, and injections follow directly from the value relation.  Lambda uses
the computation induction hypothesis after extending both environments by
related arguments.

## 3. Ordinary computation cases

### Return

The operational computation returns immediately and semantic return is
$\mathsf{ret}_W(\epsilon,d)$.  Apply the value induction hypothesis.

### Application

The function value relation instantiated with the argument value relation is
exactly the desired computation relation.

### Sequencing

Use the first computation relation.

- Bottom is preserved by strict bind.
- At return, operational `let` substitutes the returned value and semantic bind
  invokes the related continuation, prefixing the same Writer segment.
- At request, both operational and semantic bind retain the request and compose
  pointwise with the related continuation.

### Conditionals and sums

The value relation chooses the same boolean or coproduct summand, after which
the corresponding induction hypothesis applies.

### Writer primitive

`tell(w)` takes the operational Writer step and returns unit.  Its denotation is
$\mathsf{ret}_W(w,())$, so the boundary relation holds exactly.

### New free operation

The term immediately exposes the nominal request with empty Writer prefix and
identity response continuation.  This is the semantic request constructor.

## 4. Recursive-function case

Let

$$
R=\mathsf{rec}\ f(x).M
$$

and let $F$ be the continuous semantic functional induced by the body.  Its
denotation is

$$
f_\infty=\bigsqcup_{n<\omega}f_n,
\qquad
f_0=\bot,
\qquad
f_{n+1}=F(f_n).
$$

:::{prf:lemma} Recursive approximation lemma
:label: lem-recursive-function-approximation-v2

For every $n$,

$$
R\mathcal V_{A\to(B!\rho)}f_n.
$$
:::

:::{prf:proof}
By induction on $n$.

- $f_0$ maps every argument to computation bottom, which relates to every
  application.
- Suppose $R\mathcal V f_n$.  For a related argument $U\mathcal V d$, one
  operational unfolding gives

  $$
  R\,U\longrightarrow M[R/f,U/x].
  $$

  Apply the typing induction hypothesis to the body in environments extended
  by $R\mathcal V f_n$ and $U\mathcal V d$.  The resulting semantic computation
  is $F(f_n)(d)=f_{n+1}(d)$.  Closure of the computation relation under a finite
  internal step gives the result.
:::

By admissibility of the function relation,

$$
R\mathcal V\bigsqcup_n f_n=f_\infty.
$$

This discharges recursion without assuming operational termination.

## 5. Deep-handler case

Let $H=\mathsf{lfp}(\Phi_h)$ be the semantic handler.  For a continuous
candidate $g$, define $\mathcal P(g)$ to mean:

> whenever $N\mathcal C_A^{\rho\cup\{\Delta\}}t$, the operational term
> `handleDelta N with h` is related to $g(t)$.

:::{prf:lemma} Handler fixed-point induction
:label: lem-recursive-handler-fixedpoint-v2

$\mathcal P$ is admissible, $\mathcal P(\bot)$ holds, and

$$
\mathcal P(g)\Longrightarrow\mathcal P(\Phi_h(g)).
$$
:::

:::{prf:proof}
Admissibility follows pointwise from
{prf:ref}`lem-recursive-writer-admissibility-v2`.  Bottom is immediate.
For closure, inspect the related source boundary.

- Source bottom has no obligation.
- Return uses the related return clause and identical Writer prefix.
- A matching request takes the operational handler step.  Related operation
  clauses receive related parameters and resumptions; the latter use
  $\mathcal P(g)$ pointwise.
- A nonmatching request is forwarded with the pending operational handler in
  its continuation; the semantic request continuation uses $g$, and
  $\mathcal P(g)$ relates them.

The clause typing induction hypotheses supply the related clause computations,
including zero-, one-, and multi-shot uses of the resumption.
:::

Fixed-point induction gives $\mathcal P(H)$.  Combining it with the induction
hypothesis for the handled computation proves the handler typing case.

## 6. Subeffecting

Row weakening changes neither operational behavior nor constructors.  The
semantic weakening injects nominal request labels into the larger row, and the
logical relation is stable under this injection.

## 7. Consequences

For every closed well-typed term:

$$
V\mathcal V_A\llbracket V\rrbracket,
\qquad
M\mathcal C_A^\rho\llbracket M\rrbracket.
$$

Therefore every nonbottom finite denotational boundary is operationally
reflected.  Together with one-step soundness, this yields two-sided adequacy.

The proof is the classic PCF admissible-logical-relation pattern, adapted to
Writer boundaries and free requests.  The use of logical relations and
fixed-point approximation follows the computational-adequacy tradition of
[Plotkin's LCF](https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf); the
domain-relational perspective is surveyed in [Pitts' operationally based
theories](https://www.cl.cam.ac.uk/~amp12/papers/opebtp/opebtp.pdf).
