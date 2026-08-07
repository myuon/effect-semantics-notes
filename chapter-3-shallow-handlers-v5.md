# Chapter III — shallow handlers over ordered traces

## Status

**Working handler specification.**  The calculus remains recursion-free.  A
shallow handler handles one exposed request and does not reinstall itself on a
resumption.

## 1. General shallow syntax

An exhaustive handler for $\Delta$ has the standard shape

```text
shallow_Delta M with {
  return x  -> Hret;
  op_i(p,k) -> Hi;
  other op(p,k) -> Hother
}
```

where

$$
k:R_i\to(C!L_k)
$$

is the captured continuation without the surrounding handler.  Exhaustiveness
means that every operation in $\Sigma(\Delta)$ has a clause.  The optional
`other` clause exposes the continuation of a different interface.  If omitted,
its default is terminating forwarding: rebuild the request with the bare
continuation and finish this shallow handler.

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

For $\Gamma\neq\Delta$, the omitted-`other` default forwards the first
$\Gamma$ request with the original continuation and finishes this handler:

$$
\mathsf{shallow}_\Delta
 (E[\mathsf{op}_{\Gamma,j}(V)],h)
\leadsto
\mathsf{op}_{\Gamma,j}(V;\lambda r.E[\mathsf{return}\,r]).
\tag{S-Other}
$$

With an explicit `other` clause, reduction instead substitutes the request
parameter and bare continuation into that clause.  This extra observation is
not deep handling: `k` is still unwrapped.  Chapter IV uses it to write a
recursive forwarding clause that reinstalls the derived handler.

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

If the already executed prefix has effect $b$, the operation label is
$\Delta$, the response clause has effect $e'$, and the tail has effect $e$,
then

$$
b\cdot\Delta\cdot e
\longmapsto
b\cdot e'\cdot e.
\tag{Affine-Trace}
$$

This is the primary ordered law requested by the research program.

## 4. General continuation usage

The full shallow calculus distinguishes three cases.

- If the clause never calls $k$, the residual trace $e$ is discarded.
- If it calls $k$ once after trace $e'$, the result is $e'\cdot e$.
- If it calls $k$ several times, the corresponding copies of $e$ occur in the
  order induced by the clause.

Therefore the exact transformer for a general clause cannot be inferred from
an unordered clause row.  It requires either the clause's trace-language
semantics or an auxiliary usage discipline.  The affine fragment gives the
cleanest first preservation theorem.

## 5. Tree semantics

For the affine fragment, define a tree transformation that traverses base
nodes until the first free boundary:

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
=\mathsf{free}_{\Gamma,j}(p,k)
\quad(\Gamma\neq\Delta).
$$

The final equation does not recurse into $k$.

## 6. What is and is not eliminated

On a specific trace whose first exposed free request is the matching
$\Delta$, that occurrence is eliminated exactly.  This does **not** imply that
all later $\Delta$ occurrences disappear.  For example,

$$
b\cdot\Delta\cdot c\cdot\Delta\cdot e
\mapsto
b\cdot e'\cdot c\cdot\Delta\cdot e.
$$

This is not a failure of the ordered effect system.  The type records a set of
possible ordered executions, while the shallow construct transforms the first
matching boundary on each applicable execution.  Chapter IV recursively
repeats this transformation to obtain deep behavior.

## 7. Chapter-III theorem target

For exhaustive affine clauses, prove:

1. operational/tree correspondence;
2. soundness of the pathwise trace transformer;
3. preservation and effect-aware progress;
4. compatibility with the base embedding;
5. lifting of base logical relations through the handler equations;
6. ground adequacy inherited from the finite free-tree model.

The general discard/multi-shot calculus is recorded, but its strongest exact
trace theorem is conditional on a continuation-usage analysis.
