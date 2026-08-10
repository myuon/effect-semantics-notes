# Operational and denotational graded models

## Status

**Canonical architecture.** This page replaces the former presentation in
which a response monad $\mathcal K$ was placed outside a packed observation
object. Base effects live in a dedicated operational graded monad $S$ and a
denotational graded monad $T$.

## 1. Two base models

Fix a preordered monoid $B$. A base language supplies two strong $B$-graded
monads with coherent weakening,

$$
S_bA \qquad\text{and}\qquad T_bA.
$$

$S$ is the compositional operational model. Its bind performs the actual
operational sequencing of Writer output, state transitions, exceptions,
nondeterministic branches, or probability mass. $T$ is the chosen
denotational model.

Each primitive $\beta:P_\beta\to R_\beta$ has two interpretations

$$
\beta^S:P_\beta\to S_{|\beta|}R_\beta,
\qquad
\beta^T:P_\beta\to T_{|\beta|}R_\beta.
$$

There is no additional response monad outside $S$. In particular, deterministic
Writer, State, and Exception do not use $\mathsf{Id}(\mathsf{Obs})$:

$$
S^W A=W\times A,
\qquad
S^{St}A=\mathsf{Store}\to(A\times\mathsf{Store}),
\qquad
S^E A=A+\mathsf{Error}.
$$

Partiality, finite nondeterminism, and probability are likewise properties of
$S$ itself, for example by using lifted, powerset, or subdistribution
operational monads.

## 2. Base comparison

The functional presentation uses a graded monad morphism

$$
q_b:T_bA\longrightarrow S_bA
$$

that preserves return, graded bind, weakening, strength, and every base
primitive. The relational presentation instead supplies a compatible graded
relation

$$
\mathcal R_b(A)\subseteq S_bA\times T_bA.
$$

For a closed typed base computation, the comparison theorem is

$$
q_b(\llbracket M\rrbracket_T)=\llbracket M\rrbracket_S,
$$

or the corresponding relational judgment. A separate machine theorem may
identify direct small-step execution with $\llbracket M\rrbracket_S$:

$$
\mathsf{run}(M)=\llbracket M\rrbracket_S.
$$

Together these give the intended adequacy chain

$$
\mathsf{run}(M)=\llbracket M\rrbracket_S
=q_b(\llbracket M\rrbracket_T).
$$

## 3. What remains of observation

An observation is only a chosen ground predicate or result comparison used
for contextual reasoning, TT lifting, or a weaker adequacy statement. It does
not carry the effect structure used by sequencing. Writer logs, stores,
exceptions, and probability mass stay inside $S$.

Thus observation reflection is a possible consequence of the $S$--$T$
comparison, not the definition of operational effects.

## 4. Free extension

Assume the same strong graded FreeT construction exists for both models and
adjoin the first-order signature $\Sigma$:

$$
\widehat S=\mathsf F_\Sigma(S),
\qquad
\widehat T=\mathsf F_\Sigma(T).
$$

For canonical constructions, the base-action square is proved from the two
chosen FreeT action constructions. The
base comparison lifts by parameterized initiality to

$$
\widehat q:
\mathsf F_\Sigma(T)\longrightarrow\mathsf F_\Sigma(S),
$$

and

$$
\widehat q(\llbracket M\rrbracket_{\widehat T})
=\llbracket M\rrbracket_{\widehat S}.
$$

Compatible graded logical relations lift in parallel. In Lean the ungraded
finite core is [`GenericExtensionAlgebra.ModelComparisonCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparisonCert#doc),
with the lifting theorem
[`ModelComparisonCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparisonCert.lift#doc).
General categorical sufficient conditions are stated in
[FreeT existence](graded-freet-existence-v1.md).

## 5. Shallow handling and recursion

Shallow handlers preserve the comparison when corresponding clauses are
compatible with $q$ or $\mathcal R$. They act once on the exposed free layer;
no fixed point is needed in the finite theorem.

For recursive completion, one additionally requires continuity and one-layer
commutation. If

$$
q_*\circ F_T=F_S\circ q_*,
$$

then the existing fixed-point transport theorem yields

$$
q_*(\mu F_T)=\mu F_S.
$$

This is the recursive/derived-deep strengthening and is not assumed by the
finite shallow theorem.

## 6. Certificate split

The canonical records are conceptually:

1. `BaseSafetyCert(L,B)` -- syntax, typing, preservation, progress, and effect
   bounds;
2. `OperationalModelCert(L,B,S)` -- the operational graded monad and primitive
   interpretations;
3. `DenotationalModelCert(L,B,T)` -- the denotational graded monad and
   primitive interpretations;
4. `ModelComparisonCert(S,T,q)` or its relational counterpart;
5. `MachineSoundnessCert(L,S)` -- optional identification of direct execution
   with the operational model.

The old name `AdequacyCert` remains temporarily as a Lean compatibility API,
but new statements use the comparison certificate explicitly.
