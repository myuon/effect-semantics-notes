# Base observation adequacy criterion v1

## Status

**Paper-level sufficient criterion for BA, with Writer and State instances.**

The criterion replaces a term-by-term adequacy proof by one algebraic check:
the operational machine and the chosen denotational model must interpret every
primitive base operation in the same way after observation.

## 1. Operational models as graded algebras

Let $O$ be a coherent $B$-graded monad representing operational base behavior.
It may contain machine states, logs, nondeterministic outcomes, or another
chosen observation structure. Assume primitive operations

$$
\beta^O:P_\beta\to O_{|\beta|}R_\beta.
$$

The operational interpretation of a typed base tree is its canonical fold

$$
\mathsf{run}^O_b
=
\mathsf{fold}^O_b:
\mathsf{BTree}_b(X)	o O_bX.
$$

Concretely,

$$
\mathsf{run}^O_1(\mathsf{ret}(x))=\eta^O(x),
$$

$$
\mathsf{run}^O_{|\beta|c}
(\mathsf{base}_\beta(p,k))
=
\beta^O(p)
\mathbin{\mathsf{bind}^O}
(\lambda r.\mathsf{run}^O_c(k(r))),
$$

with weakening interpreted by $\tau^O$. A node-compatible machine implements
exactly these equations: execute the root request, receive a typed result, and
continue with the selected subtree.

## 2. Comparison with a chosen model

Let $T$ be the target $B$-graded monad of the denotational semantics. Suppose
there is a primitive-preserving graded monad morphism

$$
q_b:T_bX\to O_bX.
$$

Thus $q$ preserves unit, bind, weakening, and

$$
q_{|\beta|}(\beta^T(p))=\beta^O(p).
$$

### Theorem BA-001 — Fold comparison

For every $d:\mathsf{BTree}_b(X)$,

$$
\boxed{
q_b(\mathsf{fold}^T_b(d))
=
\mathsf{run}^O_b(d).
}
$$

### Proof

This is BI-006 with $U=O$. Explicitly, induction on $d$ uses unit preservation
at return, primitive and bind preservation at a base node, and weakening
preservation at `wk`. $\square$

The direction $T\to O$ is appropriate when $T$ contains at least enough
information to compute the operational observation. Equality of carriers or an
inverse map is unnecessary.

## 3. Ground observation

For a ground result set $G$, choose a final observation map

$$
o_b:O_bG\to\mathcal O.
$$

Define

$$
\mathsf{obs}_{\mathrm{op}}(d)
=
o_b(\mathsf{run}^O_b(d)),
$$

and

$$
\mathsf{obs}_T(t)=o_b(q_b(t)).
$$

### Corollary BA-002 — Base observation adequacy

For every typed base tree $d$,

$$
\boxed{
\mathsf{obs}_{\mathrm{op}}(d)
=
\mathsf{obs}_T(\mathsf{fold}^T_b(d)).
}
$$

### Proof

Apply $o_b$ to BA-001. $\square$

This is precisely assumption BA in the Conditional adequacy theorem. Hence BA
is discharged whenever the machine behavior is a graded algebra and the target
admits the primitive-preserving comparison $q$.

## 4. Preservation and reflection variants

Sometimes adequacy is phrased as a predicate rather than an exact observation.
Let $P\subseteq\mathcal O$. BA-002 gives both directions:

$$
P(\mathsf{obs}_{\mathrm{op}}(d))
\Longleftrightarrow
P(\mathsf{obs}_T(\mathsf{fold}^T(d))).
$$

If only a map $O\to T$ is available, one generally obtains soundness but not
reflection unless that map is observation-reflecting. Thus the orientation and
separation power of the comparison map matter; a monad morphism by itself is
not automatically an adequacy theorem.

## 5. Writer instance

Take

$$
B_W=\{1,w\},
\qquad
w^2=w,
\qquad
1\leq w,
$$

and

$$
O_1X=X,
\qquad
O_wX=\mathsf{List}(\mathsf{String})\times X.
$$

Operational `tell(s)` is

$$
\mathsf{tell}^O(s)=([s],*),
$$

and bind concatenates logs in order. Choosing the same Writer graded monad for
$T$ makes $q$ the identity. With

$$
o_w(\ell,x)=(\ell,x),
$$

BA-002 recovers exact ordered-log and result adequacy. The earlier Writer proof
is therefore the identity-comparison instance of BA-001.

## 6. State instance

This example checks that the criterion is not Writer-specific.

Fix a state set $S$ and operations

$$
\mathsf{get}:1\to S,
\qquad
\mathsf{put}:S\to1.
$$

Use

$$
B_S=\{1,s\},
\qquad
s^2=s,
\qquad
1\leq s.
$$

Define the graded state model

$$
T_1X=X,
\qquad
T_sX=S\to(S\times X).
$$

Weakening embeds a pure result without changing the state:

$$
\tau_{1,s}(x)=\lambda\sigma.(\sigma,x).
$$

The graded bind cases use ordinary state threading whenever either side has
grade $s$. The primitives are

$$
\mathsf{get}^T(*)
=
\lambda\sigma.(\sigma,\sigma),
$$

$$
\mathsf{put}^T(\sigma')
=
\lambda\sigma.(\sigma',*).
$$

### Operational state machine

A configuration is $(M,\sigma)$. At `get`, the machine replies with the current
state and keeps it. At `put(\sigma')`, it replies with $*$ and replaces the
state by $\sigma'$.

Let $O=T$ with these operational primitives and take $q=\mathrm{id}$. For an
initial state $\sigma_0$, choose

$$
o_{s,\sigma_0}(f)=f(\sigma_0).
$$

### Proposition BA-003 — State-machine adequacy

For every typed state-only tree $d:\mathsf{BTree}_s(X)$,

$$
\mathsf{run}_{\mathrm{machine}}(d,\sigma_0)
=
\mathsf{fold}^T_s(d)(\sigma_0).
$$

### Direct proof

Induction on $d$.

- Return leaves $\sigma_0$ unchanged and returns $x$.
- At `get`, both sides select continuation $k(\sigma_0)$ without changing the
  state; apply the induction hypothesis.
- At `put(\sigma')`, both sides select $k(*)$ in state $\sigma'$; apply the
  induction hypothesis.
- Weakening is the pure state embedding on both sides.

$\square$

Thus exact final-state/result adequacy survives the free-operation and shallow
handler extension whenever the handled behavior becomes base-only.

## 7. A non-example

Suppose $T$ interprets every base operation as the same constant and $O$
records their labels. No primitive-preserving map $q:T\to O$ can exist, because
two identified $T$ primitives would have to map to two distinct operational
observations. This is the precise reason an arbitrary graded monad
interpretation need not be adequate.

The Free extension theorem remains valid in this situation; only observational
reflection into that particular $T$ fails.

## 8. General adequacy theorem with BA discharged

### Theorem BA-004

Assume:

1. the fixed recursion-free Stage 2 calculus;
2. a node-compatible operational base model $O$;
3. a target strong $B$-graded monad $T$ interpreting the same primitives;
4. a primitive- and weakening-preserving graded monad morphism $q:T\to O$;
5. a chosen ground observation $o:O_bG\to\mathcal O$.

Then every closed handled program whose behavior is base-only satisfies exact
ground adequacy:

$$
\mathsf{obs}_{\mathrm{op}}(M)
=
o(q(\mathsf{fold}^T(d_M))).
$$

### Proof

OD-012 discharges the operational assumptions. AD-003 identifies source
behavior with its interaction tree; AD-004 commutes direct handling with the
structural handler; BI-008 supplies the typed base fold; BA-001 compares that
fold with the operational model. Apply $o$. $\square$

## 9. Remaining boundary

- The operational behavior must become base-only before using a base fold.
- The comparison map must preserve primitive operations, not merely monad unit
  and bind.
- Exact equality can be weakened to a logical relation when operational and
  denotational observations live in different sets.
- Full abstraction would additionally require contextual definability or a
  converse separation theorem.

The adequacy package is now reduced to a small, checkable algebraic interface
for each new base effect.
