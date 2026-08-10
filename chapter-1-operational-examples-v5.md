# Chapter I — operational semantics and concrete machines

:::{admonition} Lean correspondence — Chapter I
:class: tip
**Lean checked.** CBV reduction is [`LanguageStep`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep#doc), preservation is [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc), and closed progress is [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc). See the [Chapter-I correspondence table](review-guide.md#chapter-i-fixed-base-language).
:::

## Status

**Derived operational development.**  This page expands the syntax fixed in
[Chapter I](chapter-1-foundations-v5.md).  There are still no free operations,
handlers or fixed points.

## 1. Evaluation contexts and internal reduction

The fine-grain core evaluates computation positions under sequencing:

$$
\mathcal E::=[-]
\mid
\mathbf{let}\ x\leftarrow\mathcal E\ \mathbf{in}\ N.
$$

General application is evaluated left-to-right by elaboration:

```text
M N  :=  let f <- M in let x <- N in f x
```

Thus $M$ runs first, $N$ second, and only then does the latent effect of the
function body occur.  Operational proofs reason about the elaborated core.

The principal internal reductions are

$$
(\lambda x.M)V\longrightarrow M[V/x],
\tag{B-$\beta$}
$$

Here

$$
\lambda x.M:A\xrightarrow{e}B
$$

means that executing the body after application has latent effect $e$.  If

$$
\Gamma\vdash M:(A\xrightarrow{e}B)!e_M,
\qquad
\Gamma\vdash N:A!e_N,
$$

then the elaborated application has type

$$
\Gamma\vdash M\,N:B!(e_M\cdot e_N\cdot e).
$$

$$
\mathbf{let}\ x\leftarrow\mathsf{return}\,V\ \mathbf{in}\ N
\longrightarrow N[V/x],
\tag{B-Let}
$$

$$
\mathbf{if}\ \mathsf{true}\ \mathbf{then}\ M\ \mathbf{else}\ N
\longrightarrow M,
$$

$$
\mathbf{if}\ \mathsf{false}\ \mathbf{then}\ M\ \mathbf{else}\ N
\longrightarrow N,
$$

with the analogous two rules for sum elimination.  Reduction is closed under
$\mathcal E$.

A base primitive does not reduce internally.  The exposed form is

$$
\mathcal E[\beta(V)].
$$

The selected base machine observes the request and returns a response object in
$\mathcal K(R_\beta+\mathsf{Out}_\beta)$.  Every response value is plugged
into the same hole.  No continuation is a syntactic argument of $\beta$.

## 2. Generic decomposition

For a closed well-typed computation, exactly one of the following holds:

1. it is $\mathsf{return}\,V$;
2. it has a uniquely located internal redex and hence one internal reduct;
3. it decomposes uniquely as $\mathcal E[\beta(V)]$.

The proof is by induction on the computation syntax, using canonical forms for
functions, booleans, products and sums.  In a `let`, either the left computation
reduces, returns, or exposes its unique request; each case determines the
enclosing evaluation position uniquely.  Case 3 does not require the primitive
response to be unique.

## 3. Writer instance

Let messages range over an alphabet $\mathsf{Msg}$.  Use ordered word bounds

$$
B_W=\mathsf{Msg}^*,
$$

with concatenation and empty word $\epsilon$.  Let $\preceq$ be the compatible
insertion preorder on words; in particular $\epsilon\preceq w$.  This lets an
annotation contain possible writes that a particular branch may omit.  The
primitive family is

$$
\mathsf{tell}_a:1\to1,
\qquad
|\mathsf{tell}_a|=[a].
$$

A configuration is $\langle M,w\rangle$.  The external rule is

$$
\langle\mathcal E[\mathsf{tell}_a(*)],w\rangle
\longrightarrow_W
\langle\mathcal E[\mathsf{return}\,*],w\cdot[a]\rangle.
\tag{W-Tell}
$$

Consider

```text
let _ <- tell_a(*) in
let _ <- tell_b(*) in
return true
```

Its machine run is

$$
\begin{aligned}
\langle M,\epsilon\rangle
&\longrightarrow_W
\langle\mathbf{let}\ \_\leftarrow\mathsf{return}\,*\ \mathbf{in}
       \mathbf{let}\ \_\leftarrow\mathsf{tell}_b(*)\ \mathbf{in}
       \mathsf{return}\,\mathsf{true},[a]\rangle\\
&\longrightarrow_W^*
\langle\mathsf{return}\,\mathsf{true},[a,b]\rangle.
\end{aligned}
$$

The program is typed at $[a]\cdot[b]$.  Reversing the two source statements is
typed at $[b]\cdot[a]$.  The annotations distinguish their possible order, but
neither annotation is required to equal a runtime data structure.

### Application order

Let

```text
M = let _ <- tell_m(*) in
    return (fun x -> let _ <- tell_e(*) in return x)

N = let _ <- tell_n(*) in return true
```

Then

$$
\vdash M:(\mathsf{Bool}\xrightarrow{[e]}\mathsf{Bool})![m],
\qquad
\vdash N:\mathsf{Bool}![n].
$$

Expanding the derived application and applying the core `let` and value
application rules gives

$$
\vdash M\,N:\mathsf{Bool}!([m]\cdot[n]\cdot[e]).
$$

The elaborated machine first constructs the function while logging $m$, then
evaluates the argument while logging $n$, and finally executes the body while
logging $e$.  Its final Writer log is therefore $[m,n,e]$.

### Conditional Writer upper bound

For

```text
if c then tell_a(*) else return *
```

assume $1\leq[a]$.  The pure branch can be weakened from $1$ to $[a]$, so the
whole conditional has effect

$$
[a].
$$

When `c` is false, no message is written.  This is sound: $[a]$ says that the
write may happen, not that it must happen.

## 4. State instance

Let the store be Boolean and use

$$
\mathsf{get}:1\to\mathsf{Bool},
\qquad
\mathsf{put}:\mathsf{Bool}\to1.
$$

Configurations are pairs $\langle M,s\rangle$:

$$
\langle\mathcal E[\mathsf{get}(*)],s\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\,s],s\rangle,
$$

$$
\langle\mathcal E[\mathsf{put}(s')],s\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\,*],s'\rangle.
$$

Run

```text
let x <- get(*) in
let _ <- put(not x) in
return x
```

from `true`.  It yields

$$
\langle\mathsf{return}\,\mathsf{true},
\mathsf{false}\rangle.
$$

From `false`, it yields

$$
\langle\mathsf{return}\,\mathsf{false},\mathsf{true}\rangle.
$$

Both runs have the ordered upper bound
$\mathsf{read}\cdot\mathsf{write}$.  It records possible effect order, not the
concrete values read or written.

## 5. Exception instance

Fix a set $\mathsf{Err}$ and primitives

$$
\mathsf{raise}_e:1\to A
$$

for every result type $A$.  A terminal machine outcome is
$\mathsf{error}(e)$:

$$
\mathcal E[\mathsf{raise}_e(*)]
\longrightarrow_X
\mathsf{error}(e).
\tag{X-Raise}
$$

Thus

```text
let _ <- raise_boom(*) in
tell_a(*)
```

terminates at `error(boom)`; the later Writer effect is never
reached.  Conversely,

```text
let _ <- tell_a(*) in
raise_boom(*)
```

performs the Writer action before terminating at `error(boom)`.

The source typing may conservatively assign
$\mathsf{raise}\cdot\mathsf{write}$ to the first program even though the write
is unreachable.  Alternatively, a concrete abortive effect algebra may impose
$\mathsf{raise}\cdot b=\mathsf{raise}$.  This is an instance-level precision
choice, not part of the generic operational semantics.

This combined example will later check that free-operation handlers preserve
possible base effects before a handled request.

## 6. Probabilistic `random` instance

Let

$$
\mathsf{randomBool}:1\to\mathsf{Bool},
\qquad |\mathsf{randomBool}|=\mathsf{rnd},
$$

and take $\mathcal K=\mathsf{SubDist}$.  Its response kernel is

$$
\mathsf{resp}_{\mathsf{randomBool}}(*)
=\tfrac12\delta_{\mathsf{true}}+
 \tfrac12\delta_{\mathsf{false}}.
$$

Equivalently, the labelled boundary steps are

$$
\mathcal E[\mathsf{randomBool}(*)]
\xrightarrow{1/2}
\mathcal E[\mathsf{return}\,\mathsf{true}],
$$

$$
\mathcal E[\mathsf{randomBool}(*)]
\xrightarrow{1/2}
\mathcal E[\mathsf{return}\,\mathsf{false}].
$$

The evaluation context and request are unique; the response is not.  For

```text
x <- randomBool(*) in return (not x)
```

the operational observation is the distribution

$$
\tfrac12\delta_{\mathsf{true}}+
\tfrac12\delta_{\mathsf{false}},
$$

not a unique returned Boolean.

## 7. Operational conclusions

Writer, State, Exception, and probability use their own operational monads.
In every instance the next evaluation position is unique. In the
recursion-free calculus evaluation yields a well-defined element of the
chosen $S_bA$; nondeterminism or probability, when present, is structure of
$S$ rather than ambiguity in evaluation-context decomposition. These facts
become fields of the Chapter-I certificate.
