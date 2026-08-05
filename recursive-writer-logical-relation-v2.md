# Recursive Writer logical relation v2

## Status

**Adequacy relation for the fixed recursive Writer/free-handler calculus.**  It
internalizes the former appeal to an unspecified PCF adequacy theorem.  The
remaining semantic assumptions are stated explicitly as a domain package.

## 1. Domain package

Interpret each value type $A$ by a pointed or unpointed domain $D_A$ as
appropriate:

$$
D_1=1,
\qquad
D_{\mathsf{Bool}}=\{\mathsf{false},\mathsf{true}\},
$$

$$
D_{A\times B}=D_A\times D_B,
\qquad
D_{A+B}=D_A\oplus D_B,
$$

$$
D_{A\to(B!\rho)}
=
[D_A\to_c\mathsf{CWTree}_\rho D_B].
$$

Assume:

1. the domain constructors and recursive Writer domains exist;
2. semantic term constructors are continuous;
3. each primitive value constant is interpreted distinctly;
4. `tell` has its operationally correct continuous interpretation;
5. directed suprema and least fixed points are available in computation and
   function domains.

These assumptions are structural properties of the chosen CPO model, not an
adequacy theorem.

## 2. Operational boundary evaluation

For a closed computation $M$, write

$$
M\Downarrow\mathsf{ret}(w,V)
$$

or

$$
M\Downarrow\mathsf{req}(w;\Delta,i,P,K).
$$

Here $K$ is the residual operational continuation: supplying a closed response
value $U$ produces the next closed computation $K[U]$.

Evaluation is deterministic.  If neither judgment holds, the computation has
boundary divergence.

## 3. Value and computation relations

Define simultaneously:

$$
V\mathrel{\mathcal V_A}d
$$

between closed values and $d\in D_A$, and

$$
M\mathrel{\mathcal C_A^\rho}t
$$

between closed computations and
$t\in\mathsf{CWTree}_\rho D_A$.

### Ground values

Unit and booleans are related only to their corresponding semantic constants.
Primitive base values use the chosen primitive relation.

### Products and sums

$$
(V_1,V_2)\mathrel{\mathcal V_{A\times B}}(d_1,d_2)
$$

iff $V_1\mathcal V_A d_1$ and $V_2\mathcal V_B d_2$.  Injections are related
componentwise and must use the same summand.

### Functions

$$
V\mathrel{\mathcal V_{A\to(B!\rho)}}f
$$

iff for every $U\mathcal V_A d$,

$$
V\,U\mathrel{\mathcal C_B^\rho}f(d).
$$

### Computations

Bottom imposes no convergence obligation:

$$
M\mathrel{\mathcal C_A^\rho}\bot
$$

for every well-typed closed $M$.

For return:

$$
M\mathrel{\mathcal C_A^\rho}\mathsf{ret}_W(w,d)
$$

iff there is a value $V$ such that

$$
M\Downarrow\mathsf{ret}(w,V)
\quad\text{and}\quad
V\mathcal V_A d.
$$

For a request:

$$
M\mathrel{\mathcal C_A^\rho}
\mathsf{req}_W(w;\Delta,i,p,k)
$$

iff evaluation exposes the same nominal request and Writer prefix,

$$
M\Downarrow\mathsf{req}(w;\Delta,i,P,K),
$$

the parameter satisfies $P\mathcal V_{P_i}p$, and for all related responses
$U\mathcal V_{R_i}d$,

$$
K[U]\mathrel{\mathcal C_A^\rho}k(d).
$$

For non-well-founded request behavior, this clause is read coinductively, or
equivalently through all finite observations of the recursive domain.

## 4. Admissibility

:::{prf:lemma} Admissibility of the computation relation
:label: lem-recursive-writer-admissibility-v2

For each closed $M:A!\rho$, the predicate

$$
\{t\mid M\mathcal C_A^\rho t\}
$$

contains bottom and is closed under directed suprema.  Function value relations
are closed pointwise under directed suprema of semantic functions.
:::

:::{prf:proof}
Bottom is included by definition.  A finite root observation of a directed
supremum is witnessed at some stage.  Determinism ensures that all later stages
have the same return/request constructor, Writer prefix, nominal label, and
parameter observation.  Value relations are admissible by induction on type;
request continuations use the coinduction hypothesis pointwise.  Function
spaces use pointwise suprema and the computation case.
:::

This is the exact property needed to pass from finite recursive approximants to
their least fixed point.

## 5. Environment relation

For

$$
\Gamma=x_1:A_1,\ldots,x_n:A_n,
$$

relate a closing substitution $\gamma$ and semantic environment $\eta$ when

$$
\gamma(x_j)\mathcal V_{A_j}\eta(x_j)
$$

for every variable.  Write this as

$$
\gamma\mathrel{\mathcal G_\Gamma}\eta.
$$

## 6. Why this relation proves reflection

If

$$
M\mathcal C_A^\varnothing\llbracket M\rrbracket
$$

and $\llbracket M\rrbracket=\mathsf{ret}_W(w,d)$, the definition immediately
produces an operational Writer return with the same $w$.  If the denotation is
bottom, the relation makes no claim; divergence reflection is obtained later
by determinism and the impossibility of an empty-row request.

The relation therefore supplies precisely the missing semantic-to-operational
direction without assuming full abstraction or normalization.
