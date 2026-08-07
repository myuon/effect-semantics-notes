# Chapter I — metatheory and base certificate

## Status

**Paper proof package.**  This page extracts exactly what Chapter II may assume
when it adds free operations.

## 1. Syntactic substitution

### Lemma I.1 — value substitution

If

$$
\Gamma,x:A\vdash V:B
\qquad
\Gamma\vdash W:A,
$$

then

$$
\Gamma\vdash V[W/x]:B.
$$

### Lemma I.2 — computation substitution

If

$$
\Gamma,x:A\vdash M:C!b
\qquad
\Gamma\vdash W:A,
$$

then

$$
\Gamma\vdash M[W/x]:C!b.
$$

Both are proved simultaneously by induction on typing.  The primitive case
uses substitution only in its parameter; no continuation case exists.

## 2. Preservation and decomposition

### Theorem I.3 — internal preservation

If

$$
\Gamma\vdash M:A!b
\qquad
M\longrightarrow M',
$$

then

$$
\Gamma\vdash M':A!b.
$$

The $\beta$ and `let-return` cases use Lemma I.2.  Branch rules retain the
declared common effect.  Context closure uses associativity of graded
sequencing.

### Theorem I.4 — unique decomposition

Every closed well-typed base computation is uniquely a return, an internal
redex in its evaluation context, or an exposed base request
$\mathcal E[\beta(V)]$.

This is the effect-aware progress theorem used by later chapters.  It does not
call an exposed request “stuck.”

## 3. Termination

### Theorem I.5 — recursion-free machine normalization

Assume every base request either produces one typed response or a classified
terminal base outcome.  Then every closed well-typed Chapter-I program reaches
a unique final base observation.

### Proof sketch

Use the standard reducibility argument for fine-grain CBV STLC.  The primitive
case is reducible by the base-package termination assumption.  Function,
product and sum cases are standard.  Unique decomposition plus deterministic
base response gives uniqueness.

The theorem is deliberately absent from the Chapter-IV certificate.

## 4. Denotational soundness

### Lemma I.6 — semantic substitution

For a computation $M$,

$$
\llbracket M[W/x]\rrbracket
=
\llbracket M\rrbracket
\circ
\langle\mathsf{id},\llbracket W\rrbracket\rangle.
$$

The `let` case uses naturality of strength and multiplication.  The primitive
case is ordinary composition with $\beta^T$.

### Theorem I.7 — internal reduction soundness

If $M\to M'$, then

$$
\llbracket M\rrbracket=\llbracket M'\rrbracket.
$$

The principal equations are semantic substitution, the graded unit laws, and
coproduct elimination.  Context closure uses congruence of graded bind.

## 5. Trace soundness

### Theorem I.8

If

$$
\vdash M:A!L
$$

and the base machine produces runtime behavior $(t,q)$, then

$$
(t,q)\in\gamma(L),
$$

where $\gamma$ is the grade concretization fixed by the base package.

### Proof

Preserve the invariant

$$
\mathsf{done}\mathbin{;}
\gamma(L_{\mathsf{residual}})
\subseteq
\gamma(L_{\mathsf{declared}})
$$

across every machine step.  Internal steps leave the completed behavior
unchanged.  A primitive step moves its leading event from the residual
computation into $\mathsf{done}$.  Sequencing uses completion-sensitive
composition; branch
selection uses membership in the chosen union.  A base abort absorbs the
residual effect; at a final return the residual behavior is
$(\epsilon,\checkmark)$.

## 6. Adequacy schema

Choose a ground observation map $\mathsf{obs}_B$ and denotational observation
$\mathsf{observe}$.  The base package is adequate at ground type $G$ when

$$
M\Downarrow_B o
\quad\Longleftrightarrow\quad
\mathsf{observe}(\llbracket M\rrbracket)=o
$$

for every closed $M:G!L$.  One direction may be selected instead if the later
application needs only soundness or reflection; the certificate records which.

### Writer instance

For the exact Writer model,

$$
\langle M,\epsilon\rangle
\Downarrow_W
\langle\mathsf{return}\,V,w\rangle
\quad\Longleftrightarrow\quad
\mathsf{observe}(\llbracket M\rrbracket)=(w,V).
$$

The proof iterates the one-step invariant that accumulated machine log followed
by residual denotational log is constant.

### State instance

For every initial store $s$,

$$
\langle M,s,\epsilon\rangle
\Downarrow_S
\langle\mathsf{return}\,V,s',t\rangle
$$

iff

$$
\llbracket M\rrbracket(s)=(V,s',t).
$$

### Exception instance

The denotation returns $(t,\mathsf{inl}\,V)$ exactly for a machine return and
$(t,\mathsf{inr}\,e)$ exactly for the terminal error $e$.  The proof follows
the short-circuiting bind equations.

## 7. The Chapter-I structure theorem

### Theorem I.9 — Base certificate extraction

Each of the exact Writer, state-and-trace, and exception-and-trace instances
supplies a structure

$$
\mathsf{BaseCert}(B,\Sigma_B,T,\mathsf{obs}_B)
$$

containing:

1. deterministic typed CBV dynamics;
2. substitution and internal preservation;
3. unique return/redex/request decomposition;
4. recursion-free normalization to a classified observation;
5. ordered trace soundness;
6. a strong graded denotational interpretation;
7. semantic substitution and reduction soundness;
8. the instance's declared ground adequacy theorem.

### Proof

Items 1–5 follow from Theorems I.3–I.5 and I.8 after checking each primitive
machine rule.  Items 6–7 follow from the concrete graded constructions and
Theorems I.6–I.7.  The three adequacy instances above provide item 8.  No free
operation or handler property is used. $\square$

## 8. Boundary exported to Chapter II

`BaseCert` does not assert that every base has exact grades, that every
denotation exposes a syntactic head event, or that base effects commute with
future free operations.  Chapter II must add visible free-operation nodes
without inspecting an opaque base computation and must prove conservativity
through the supplied embedding.
