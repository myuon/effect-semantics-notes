# Quantitative row extension v2

## Status

**Optional refinement of the completed unordered theorem.** The core theorem is
first proved for affine resumptions.  A usage-bounded multi-shot upper bound is
given separately.

## 1. Quantitative rows

Let

$$
\mathbb N_\infty=\mathbb N\cup\{\infty\}.
$$

A quantitative row is a function

$$
\nu:\mathcal D\to\mathbb N_\infty.
$$

$\nu(\Delta)$ bounds how many operations belonging to interface $\Delta$ may
occur along one execution path.

The ordinary row is its support:

$$
\operatorname{supp}(\nu)
=
\{\Delta\mid\nu(\Delta)>0\}.
$$

An ordinary unquantified row can be embedded by assigning $\infty$ to every
present label.

## 2. Algebra

Order is pointwise:

$$
\nu\leq\mu
\iff
\forall\Delta.\ \nu(\Delta)\leq\mu(\Delta).
$$

Sequential composition adds counts:

$$
(\nu+\mu)(\Delta)=\nu(\Delta)+\mu(\Delta).
$$

Branching takes pointwise maximum:

$$
(\nu\sqcup\mu)(\Delta)
=
\max(\nu(\Delta),\mu(\Delta)).
$$

The zero vector is the pure new-effect annotation.  Addition is associative and
monotone and distributes over pointwise maximum.

## 3. Typing rules

A primitive request has unit count

$$
\mathbf 1_\Delta(\Gamma)
=
\begin{cases}
1&\Gamma=\Delta,\\
0&\Gamma\neq\Delta.
\end{cases}
$$

Thus

$$
\Gamma\vdash\operatorname{op}_{\Delta,i}(V)
:R_i!\mathbf 1_\Delta.
$$

Sequencing uses $+$, conditionals use $\sqcup$, and subeffecting uses pointwise
order.

For example,

```text
if b then opΔ() else return ()
```

has count

$$
\Delta^{\leq1},
$$

without introducing a type-level operation/return sum.

## 4. Path-counted resumption trees

For a well-founded resumption $t$, define

$$
\mathsf{count}(t)(\Delta)
$$

as the supremum, over all response branches and complete paths, of the number
of $\Delta$ request nodes on that path.  Base layers contribute zero.

Define the refined carrier

$$
\mathsf{Res}_{T,\nu}A
=
\{t\mid\mathsf{count}(t)\leq\nu\}.
$$

:::{prf:theorem} Quantitative resumption grading
:label: thm-count-resumption-grading-v2

The generic resumption monad restricts to

$$
\eta:A\to\mathsf{Res}_{T,0}A,
$$

$$
\mathsf{Res}_{T,\nu}A\times
(A\to\mathsf{Res}_{T,\mu}C)
\to
\mathsf{Res}_{T,\nu+\mu}C,
$$

with weakening by pointwise inequality.
:::

:::{prf:proof}
Every path of a bind consists of one path through the first computation followed
by one path through the selected continuation.  Counts therefore add.  Return
contributes zero, and pointwise upper bounds are preserved by weakening.
:::

The support map is sound:

$$
\mathsf{Res}_{T,\nu}A
\to
\mathsf{Res}_{T,\operatorname{supp}(\nu)}A.
$$

Thus every quantitative theorem implies the corresponding unordered-row
theorem after forgetting counts.

## 5. Affine deep handlers

For the first quantitative theorem, require that every matching clause uses its
resumption at most once along each execution path.

Let:

- input count be $\nu$;
- $n=\nu(\Delta)$;
- $\kappa$ be a common pointwise upper bound on the direct new-operation count
  of any one matching clause, excluding the supplied resumption;
- $\tau$ bound the return clause;
- $\nu\setminus\Delta$ set the $\Delta$ component to zero.

Scalar multiplication is repeated vector addition.

:::{prf:theorem} Affine quantitative deep-handler bound
:label: thm-affine-count-handler-v2

An exhaustive affine deep handler has the sound count transformer

$$
\Phi^{\mathrm{aff}}_{\Delta,\kappa,\tau}(\nu)
=
(\nu\setminus\Delta)+n\kappa+\tau.
$$
:::

:::{prf:proof}
Follow one source path.  It contains at most $n$ matching $\Delta$ nodes, so at
most $n$ matching clauses are entered.  Affine use prevents a captured suffix
from being duplicated; discarding it can only reduce source counts.  Every
entered clause contributes at most $\kappa$.  A completed handled path invokes
the return clause at most once, contributing $\tau$.  Matching source nodes are
removed, giving $\nu\setminus\Delta$.
:::

If clauses and return are $\Delta$-free, then

$$
\Phi^{\mathrm{aff}}_{\Delta,\kappa,\tau}(\nu)(\Delta)=0.
$$

This quantitatively strengthens ordinary deep discharge.

The bound is an upper bound, not always exact.  An affine clause may discard a
continuation, and conditional source requests may not occur.

## 6. Exactly-once specialization

If every clause resumes exactly once, source continuation counts are not lost
or duplicated.  The same upper transformer applies, but stronger lower/exact
claims may be possible when:

- source counts are exact rather than upper bounds;
- every path reaches the relevant request;
- clauses themselves have exact path-independent counts.

Those are must/exact refinements and are not part of the current may-count
system.

## 7. Usage-bounded multi-shot handlers

Suppose every clause invokes its resumption at most $m$ times along a path, and
the original path has at most $n$ handled requests.

Define the geometric invocation bound

$$
G_m(n)=
\begin{cases}
n&m=1,\\
\dfrac{m^n-1}{m-1}&1<m<\infty,\\
0&n=0,\\
\infty&m=\infty\text{ and }n>0.
\end{cases}
$$

and a safe suffix-duplication factor

$$
D_m(n)=\max(1,m^n).
$$

:::{prf:conjecture} Usage-bounded multi-shot count bound
:label: conj-multishot-count-handler-v2

A sound coarse transformer is

$$
D_m(n)(\nu\setminus\Delta)
+G_m(n)\kappa
+D_m(n)\tau.
$$
:::

The intuition is that a request at depth $j$ can be reached through at most
$m^j$ duplicated resumptions.  Original residual requests and terminal return
paths may be duplicated by at most $m^n$, while matching clause invocations sum
geometrically.

This is left as a conjecture because arbitrary response branching, affine paths,
and the exact definition of “uses its resumption at most $m$ times” need a
usage-typed operational judgment.  It should not be promoted to the main
theorem before that judgment is fixed.

## 8. What counts say about clause invocation

In the affine fragment,

$$
\nu(\Delta)=n
$$

implies that the matching clause executes at most $n$ times per path.  This is
new information absent from unordered rows.

Consequently, if one invocation has an old base effect abstraction $e$, we know
that at most $n$ invocations must be accounted for.  But turning that fact into
one old base grade still requires an operation such as

$$
\mathsf{repeat}^{\le n}_E(e)
$$

and an interaction law describing where those effects may occur relative to
the original base behavior.

Counts solve the multiplicity question.  They do not by themselves solve
noncommutative insertion order or old/new handler scope.

## 9. Preservation of the unordered theorem

All unordered properties remain valid by applying the support abstraction:

- free-row preservation;
- empty-row safety;
- deep discharge;
- base conservativity;
- resumption monad and fold;
- morphism and logical-relation lifting;
- conditional adequacy.

The quantitative layer changes grades and handler bounds, not the underlying
runtime semantics.
