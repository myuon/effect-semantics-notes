# Common free-handler calculus v2

## Status

**Proposed common syntax and direct operational semantics.** This calculus is
the shared added fragment for the Pure, Writer, State, and Exception instances.
It intentionally does not yet define a universal base-effect grade.

## 1. Design separation

We track two things separately.

1. The **new free-effect row** records which user-defined interfaces may escape.
2. Each concrete instance supplies its own annotation and semantics for old
   base effects.

The common judgment is therefore written provisionally as

$$
\Gamma\vdash M:A!\rho,
$$

where $\rho$ mentions only newly added interfaces.  A base primitive has empty
free row even though it may be effectful in the base system.

When a concrete base judgment $\Gamma\vdash_B M:A!b$ is available, the full
instance may display both components as

$$
\Gamma\vdash M:A!(b;\rho).
$$

No generic rule for transforming $b$ through a handler is assumed here.

## 2. Interfaces

Let $\mathcal D$ be a set of interface names.  Each interface $\Delta$ has a
finite signature

$$
\Sigma(\Delta)=
\{\operatorname{op}_i:P_i\to R_i\}_{i\in I_\Delta}.
$$

Interface names are nominal.  Two operations with the same parameter and
response types but belonging to distinct interfaces are not interchangeable.

## 3. Types and terms

The initial type grammar is

$$
A,B::=1\mid\mathsf{Bool}\mid A\to(B!\rho).
$$

The arrow records the free row of the computation returned by a value-level
function.  A concrete base instance refines it to $A\to(B!(b;\rho))$.

Values and computations are separated:

$$
\begin{aligned}
V,W::={}&x\mid()\mid\mathsf{true}\mid\mathsf{false}\mid\lambda x.M,\\
M,N::={}&\operatorname{return}V
\mid V\,W
\mid\mathbf{let}\ x\leftarrow M\ \mathbf{in}\ N\\
&\mid\mathbf{if}\ V\ \mathbf{then}\ M\ \mathbf{else}\ N
\mid\beta(V)
\mid\operatorname{op}_{\Delta,i}(V)\\
&\mid\operatorname{handle}_{\Delta}M\operatorname{with}h.
\end{aligned}
$$

$\beta$ ranges over base primitives supplied by the concrete instance.
Source-level operations do not contain a continuation argument.

## 4. Handler syntax

An exhaustive handler for $\Delta$ has the form

$$
\begin{aligned}
h=\{&\operatorname{return}(x)\mapsto M_{\mathrm{ret}};\\
&\operatorname{op}_i(p,k)\mapsto M_i\}_{i\in I_\Delta}.
\end{aligned}
$$

The variable $k$ denotes a resumption.  It is an ordinary value-level function
in clause bodies and may be unused, used once, or used several times.  This
permits affine, linear, and multi-shot programs in one syntax.

The handler is exhaustive only for its named interface $\Delta$.  Operations
from another interface $\Gamma$ are forwarded rather than matched by an
`otherwise` source clause.

## 5. Free-row typing

Rows are finite sets with union and inclusion:

$$
\rho,\sigma\in\mathcal P_{\mathrm{fin}}(\mathcal D).
$$

The standard pure, application, sequencing, and conditional rules use the
empty row or union.  The characteristic rules are:

$$
\frac{
\operatorname{op}_i:P_i\to R_i\in\Sigma(\Delta)
\qquad
\Gamma\vdash V:P_i
}{
\Gamma\vdash\operatorname{op}_{\Delta,i}(V):R_i!\{\Delta\}
}
\tag{T-Op}
$$

and

$$
\frac{
\Gamma\vdash M:A!\rho
\qquad
\rho\subseteq\sigma
}{
\Gamma\vdash M:A!\sigma
}.
\tag{T-Sub}
$$

Every base primitive is free-row silent:

$$
\frac{
\beta:P_\beta\to R_\beta
\qquad
\Gamma\vdash V:P_\beta
}{
\Gamma\vdash\beta(V):R_\beta!\varnothing
}.
\tag{T-Base-Projection}
$$

This says only that $\beta$ is not a newly added free request.  It does not
claim that $\beta$ is pure.

## 6. Handler typing

Suppose the handled computation has row $\rho\cup\{\Delta\}$ with
$\Delta\notin\rho$.  Choose an
outward row $\omega$ satisfying

$$
\rho\subseteq\omega.
$$

The return clause is checked by

$$
\Gamma,x:A\vdash M_{\mathrm{ret}}:C!\omega.
$$

Each operation clause is checked by

$$
\Gamma,p:P_i,k:R_i\to(C!\omega)\vdash M_i:C!\omega,
$$

where applications of $k$ are assigned result row $\omega$.  Thus the
resumption is a computation-producing function

$$
k:R_i\to(C!\omega).
$$

Then

$$
\frac{
\Gamma\vdash M:A!(\rho\cup\{\Delta\})
\qquad
\Gamma\vdash h:(A,\Delta)\Rightarrow_\omega C
\qquad
\Delta\notin\rho
\qquad
\rho\subseteq\omega
}{
\Gamma\vdash\operatorname{handle}_{\Delta}M\operatorname{with}h:C!\omega
}.
\tag{T-Handle}
$$

The row $\omega$ includes nonmatching effects forwarded from $\rho$ and effects
performed by clauses.  If a clause explicitly re-emits $\Delta$, then
$\Delta\in\omega$ and elimination is not claimed.

This rule is intentionally an initial monomorphic presentation.  Row variables
and principal inference are postponed.

## 7. Evaluation contexts

Ordinary CBV computation contexts are

$$
E::=[]
\mid\mathbf{let}\ x\leftarrow E\ \mathbf{in}\ N
\mid\operatorname{handle}_{\Gamma}E\operatorname{with}h.
$$

For a fixed interface $\Delta$, define $\Delta$-transparent contexts:

$$
E^{\Delta}::=[]
\mid\mathbf{let}\ x\leftarrow E^{\Delta}\ \mathbf{in}\ N
\mid\operatorname{handle}_{\Gamma}E^{\Delta}\operatorname{with}h
\quad(\Gamma\neq\Delta).
$$

Such a context contains no intervening handler for $\Delta$.  It may contain
handlers for other interfaces.  This expresses nearest-matching-handler
semantics without giving source operations explicit continuation syntax.

## 8. Direct reduction rules

The ordinary rules include

$$
\mathbf{let}\ x\leftarrow\operatorname{return}V\ \mathbf{in}\ N
\longrightarrow N[V/x],
$$

$$
(\lambda x.M)V\longrightarrow M[V/x],
$$

and the two Boolean branches.

The handler return rule is

$$
\operatorname{handle}_{\Delta}(\operatorname{return}V)\operatorname{with}h
\longrightarrow
M_{\mathrm{ret}}[V/x].
\tag{H-Ret}
$$

For a matching operation, let its clause be
$\operatorname{op}_i(p,k)\mapsto M_i$.  Then

$$
\begin{aligned}
&\operatorname{handle}_{\Delta}
  E^{\Delta}[\operatorname{op}_{\Delta,i}(V)]
  \operatorname{with}h\\
&\quad\longrightarrow
M_i\left[
V/p,
\left(\lambda y.
\operatorname{handle}_{\Delta}
E^{\Delta}[\operatorname{return}y]
\operatorname{with}h\right)/k
\right].
\end{aligned}
\tag{H-Op-Deep}
$$

The reinstalled handler inside $k$ is the definition of deep resumption.
Nonmatching handlers already present in $E^\Delta$ are retained.

## 9. Forwarding is decomposition, not termination

There is no reduction rule that deletes a nonmatching handler.  If no matching
handler for $\Gamma$ exists, a closed computation can be uniquely exposed as

$$
E^\Gamma[\operatorname{op}_{\Gamma,j}(V)].
$$

Its meta-level request continuation is

$$
K=\lambda y.E^\Gamma[\operatorname{return}y].
$$

If $E^\Gamma$ contains a pending $\Delta$ handler, then $K$ contains it too.
Consequently, an enclosing $\Gamma$ handler may resume into the pending
$\Delta$ handler.  Forwarding therefore differs from the previous semantics in
which the shallow handler ended at the first nonmatching free request.

## 10. Deep versus shallow in this calculus

The distinction occurs after a matching request.

- Deep resumption uses

  $$
  \lambda y.\operatorname{handle}_{\Delta}
  E^\Delta[\operatorname{return}y]\operatorname{with}h.
  $$

- A shallow variant would pass

  $$
  \lambda y.E^\Delta[\operatorname{return}y]
  $$

  to the matching clause.

Both variants may retain a pending handler while forwarding a nonmatching
request.  Thus “shallow” does not mean “stop at the first request of any
interface.”

## 11. Immediate metatheoretic obligations

Before proving a general theorem, each concrete base must validate:

1. context decomposition relative to nearest matching handlers;
2. substitution, including resumption substitution;
3. preservation of the free-row projection;
4. effect-aware progress;
5. exhaustive deep elimination;
6. compatibility of its base transition rules with ordinary contexts and
   handler decomposition.

The syntax and rules above are frozen only after the Writer calculations reveal
no ambiguity.
