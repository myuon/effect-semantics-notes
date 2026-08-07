# Chapter IV — detailed recursive and derived-deep proofs

## 1. One-step recursion safety

:::{prf:theorem} Recursive one-step progress and preservation
:label: thm-iv-one-step-safety-v5

A closed typed computation is a classified boundary or has one unique next
step; every next step preserves its type and ordered may-effect bound.
:::

**Proof.** Extend the Chapter-III decomposition induction with the recursive
call form.  Once its argument is a value, the unique rule unfolds the body.
Typing inversion gives the body under $f:A\xrightarrow{e}B$ and $x:A$; simultaneous
substitution of the recursive closure and argument proves preservation.  All
other cases are Chapter III. $\square$

A maximal-run corollary, proved by repeatedly applying this theorem, says that
a run reaches a boundary or is infinite.  This is not itself an extra progress
case.

## 2. Approximation lemma

Let `loop_n` be the derived handler loop with recursive calls replaced by
`loop_{n-1}` and `loop_0=\bot`.

:::{prf:lemma} Source/semantic approximants
:label: lem-iv-approximants-v5

For every $n$,

$$
\llbracket\mathsf{loop}_n\rrbracket=\mathcal D_h^n(\bot).
$$
:::

**Proof.** Induction on $n$.  The zero case is the interpretation of the
undefined computation.  For $n+1$, unfold once.  Chapter-III commutation turns
the outer shallow handler into $\mathsf{sh}_{\Delta,h[g]}$, and the induction
hypothesis replaces each recursively wrapped continuation by
$g=\mathcal D_h^n(\bot)$.  This is exactly
$\mathcal D_h^{n+1}(\bot)$. $\square$

Continuity and the `RecBaseCert` source-fixpoint agreement now give

$$
\llbracket\mathsf{loop}\rrbracket
=\bigsqcup_n\llbracket\mathsf{loop}_n\rrbracket
=\bigsqcup_n\mathcal D_h^n(\bot)
=\operatorname{lfp}(\mathcal D_h).
$$

This proves derived/deep coincidence.

## 3. Operational elimination invariant

Define $P(C)$ to mean: no finite reduction prefix of $C$ ends at an exposed
$\Delta$ request outside a pending derived handler.  Prove $P(\mathsf{loop}_n
M)$ by induction on $n$ and the length of the finite prefix.  Return terminates
inside the return clause.  A matching request enters an exhaustive clause;
every matching resumption is `loop_{n-1}(k r)`, covered by induction.  A
nonmatching request is outwardly visible, but its stored continuation retains
the structurally recursive shallow handler.  Old steps preserve the pending handler.  A clause-emitted
$\Delta$ is excluded by hypothesis.  Thus every finite approximant has $P$.

For the actual fixpoint, any finite operational prefix uses only finitely many
unfoldings and is therefore a prefix of some approximant.  Hence it has $P$.
This proves operational deep elimination without assuming termination.
Admissibility gives the parallel denotational statement at the supremum.

## 4. Recursive logical relation

Take the Chapter-III relation and require admissibility: it contains bottom
and is closed under suprema of increasing chains.  The fundamental lemma is a
typing induction.  The only new case forms a continuous functional on related
function pairs.  Starting from related bottoms, compatibility maps related
approximants to related approximants; induction relates every pair
$F^n(\bot)$, and admissibility relates their suprema.  The derived handler case
uses the approximation lemma and Chapter-III handler compatibility at every
stage.  Applying the observation-reflection field proves finite-boundary
adequacy.  Bottom or productive-trace reflection follows only if it is a field
of `RecBaseCert`.

## 5. Ordered iteration bound

Let $K(e)=e^*$ be monotone with $1\le e^*$ and
$e\cdot e^*\le e^*$.  Induction gives $e^n\le e^*$ for every $n$: the zero
case is the unit inequality; the successor case is
$e^{n+1}=e\cdot e^n\le e\cdot e^*\le e^*$.

For a closure-compatible handler transformer, Chapter III gives at each
unfolding, for $\Delta$-free $b$,

$$
\Phi_h(b\cdot\Delta\cdot e)\le b\cdot e'\cdot e.
$$

Induction on approximants preserves the order of all factors.  Monotonicity
then places every transformed finite approximation below
$(b\cdot e'\cdot e)^*$.  The effect-safety interpretation concerns finite
execution prefixes, so this uniform bound covers the recursive computation.
No equality or exact multiplicity follows.

## 6. Assembly of `DeepCert`

One-step safety supplies recursive preservation and progress; the
source/semantic approximation lemma supplies definability and the deep
equations; the invariant supplies interface elimination; the admissible
logical relation supplies adequacy; and the iteration induction supplies the
ordered bound.  Old terms contain neither recursion nor derived-handler
expansion, so Chapter-III conservativity remains literal.  These fields are
exactly `DeepCert`; every stronger observation remains explicitly conditional.
