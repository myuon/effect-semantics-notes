# Chapter III — shallow handlers over ordered effects

## Status

**Working handler specification.**  The calculus remains recursion-free.  A
shallow handler transparently crosses unrelated requests, handles the first
matching request, and does not reinstall itself on that matching resumption.

## 1. General shallow syntax

An exhaustive handler for $\Delta$ has the standard shape

```text
shallow_Delta M with {
  return x  -> Hret;
  op_i(p,k) -> Hi
}
```

where

$$
k:R_i\xrightarrow{e_k}C
$$

is the captured continuation without the surrounding handler.  Exhaustiveness
means that every operation in $\Sigma(\Delta)$ has a clause.  Operations from
another interface are transparently forwarded with this handler retained in
their continuations.  Evaluation can therefore cross unrelated operations
while searching for the first matching $\Delta$ request.

## 2. Direct operational rules

For a return,

$$
\mathsf{shallow}_\Delta(\mathsf{return}\,V,h)
\longrightarrow H_{\mathsf{ret}}[V/x].
\tag{S-Ret}
$$

For a matching exposed request,

$$
\begin{aligned}
&\mathsf{shallow}_\Delta
  (E[\mathsf{op}_{\Delta,i}(V)],h)\\
&\quad\longrightarrow
H_i[V/p,(\lambda r.E[\mathsf{return}\,r])/k].
\end{aligned}
\tag{S-Match}
$$

There is no `shallow` around $E[\mathsf{return}\,r]$.  That absence is the
definition of shallowness.

For $\Gamma\neq\Delta$, forwarding preserves the pending handler:

$$
\mathsf{shallow}_\Delta
 (E[\mathsf{op}_{\Gamma,j}(V)],h)
\leadsto
\mathsf{op}_{\Gamma,j}
(V;\lambda r.\mathsf{shallow}_\Delta
(E[\mathsf{return}\,r],h)).
\tag{S-Other}
$$

This recursive occurrence is structural: in the recursion-free calculus it
descends into a proper continuation subtree.  At a matching node the clause
still receives the bare continuation.  That asymmetry is the definition of
shallow handling used here.

## 3. Affine response fragment

The earlier response-only notation

```text
with { op_i(p) -> R_i }
```

is retained as sugar for a clause that computes a response and invokes the
continuation exactly once:

```text
op_i(p,k) -> let r <- R_i in k r
```

If the already executed prefix has $\Delta$-free effect $b$, the first
matching operation label is $\Delta$, the response clause has effect $e'$, and
the tail has effect $e$, then

$$
b\cdot\Delta\cdot e
\longmapsto
b\cdot e'\cdot e.
\tag{Affine-Effect}
$$

This is the primary ordered law requested by the research program.

Because the input annotation is only an upper bound, a program typed at
$b\cdot\Delta\cdot e$ may reach a value without performing $\Delta$.  That
path has bound $b\cdot e$.  If

$$
1\leq e',
$$

then monotonicity gives

$$
b\cdot e
\leq
b\cdot e'\cdot e,
$$

so matching and no-operation paths share the advertised output bound.  Without
this optionality condition the typing rule must choose some larger common upper
bound.  The handler equation itself does not assert that a match occurred.

## 4. General continuation usage

The full shallow calculus distinguishes three cases.

- If the clause never calls $k$, the residual bound $e$ need not appear in the
  output bound.
- If it calls $k$ once after effect $e'$, a sound result is $e'\cdot e$.
- If it calls $k$ several times, the corresponding copies of $e$ occur in the
  static order induced by the clause.

Therefore a precise transformer for a general clause requires a continuation
usage discipline.  A coarser common upper bound remains possible, but the
affine fragment gives the cleanest first preservation theorem.

## 5. Tree semantics

For the affine fragment, define a tree transformation that traverses base
nodes and nonmatching free nodes until the first matching boundary:

$$
\mathsf{sh}_{\Delta,h}(\mathsf{ret}(a))
=\llbracket H_{\mathsf{ret}}[a/x]\rrbracket,
$$

$$
\mathsf{sh}_{\Delta,h}(\mathsf{base}_\beta(p,k))
=\mathsf{base}_\beta(p,r\mapsto\mathsf{sh}_{\Delta,h}(k(r))),
$$

$$
\mathsf{sh}_{\Delta,h}(\mathsf{free}_{\Delta,i}(p,k))
=\llbracket R_i[p/x]\rrbracket\mathbin{\gg=}k,
$$

$$
\mathsf{sh}_{\Delta,h}(\mathsf{free}_{\Gamma,j}(p,k))
=\mathsf{free}_{\Gamma,j}
(p,r\mapsto\mathsf{sh}_{\Delta,h}(k(r)))
\quad(\Gamma\neq\Delta).
$$

The final equation recurses into $k$; the matching equation does not.

## 6. What is and is not eliminated

When evaluation exposes a matching $\Delta$, the corresponding occurrence in
the static bound can be replaced as follows.  This does **not** imply that all
later possible $\Delta$ occurrences disappear.  For example,

$$
b\cdot\Delta\cdot c\cdot\Delta\cdot e
\mapsto
b\cdot e'\cdot c\cdot\Delta\cdot e.
$$

This is not a claim that runtime produced the entire input word.  It is a sound
type-level transformation of a may-effect upper bound.  Chapter IV recursively
repeats the shallow operation to obtain deep behavior.

## 7. Chapter-III theorem target

For exhaustive affine clauses, with $b$ containing no $\Delta$, prove:

1. operational/tree correspondence;
2. soundness of the ordered effect-bound transformer;
3. preservation and effect-aware progress;
4. compatibility with the base embedding;
5. preservation of the structural relation and graded TT relation through
   the handler equations;
6. ground adequacy inherited from the finite free-tree model.

The general discard/multi-shot calculus is recorded, but its strongest precise
effect theorem is conditional on a continuation-usage analysis.

The full Chapter-III cycle is developed in:

- [Direct shallow semantics and programs](chapter-3-operational-examples-v5.md);
- [Denotational shallow handling](chapter-3-denotational-v5.md);
- [Proofs and `ShallowCert`](chapter-3-certificate-v5.md).
