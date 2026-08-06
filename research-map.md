# Research map

## 2026-08-06 two-chapter organization

The active development now begins with [Two-chapter research program v4](two-chapter-program-v4.md).
Chapter I fixes a recursion-free first-boundary shallow matcher, computes its
behavior for [Writer, State and Exception](finite-shallow-concrete-examples-v4.md),
and extracts the [finite shallow structure-preservation theorem](finite-shallow-preservation-theorem-v4.md).
Chapter II will then add recursion and deep reinstallation.  The two axes remain
logically distinct even though the exposition follows this diagonal.

Chapter II now begins with a [primary-source literature audit](recursive-deep-literature-audit-v4.md),
then fixes the [recursive/deep calculus and resumption semantics](recursive-deep-calculus-semantics-v4.md).
The theorem is intentionally delayed until after the
[recursive Writer, State and Exception calculations](recursive-deep-concrete-examples-v4.md)
and the [adequacy reconstruction](recursive-deep-adequacy-v4.md).  The resulting
[certificate-transport theorem v4](recursive-deep-preservation-theorem-v4.md)
separates safety, semantic iteration, observation adequacy and optional
handler/base interaction assumptions.

> **Current positioning:** the free/resumption construction, deep-handler fold and
> generic safety/adequacy ingredients are substantially prior art.  The live target is
> now a certificate-transport theorem plus a sharp handler/base interaction boundary.
> See [the v3 novelty audit](novelty-audit-main-theorem-v3.md) and
> [the revised research position](research-position-after-audit-v3.md).

## 2026-08-05 方針更新

現在の本線は、特定の ordered effect calculus を完成させることではない。

> 既存の effectful language を base として固定したとき、user-defined free operations と handlers を後付けできる範囲はどこまでか。何が自動的に保存され、何が base effect との interaction law を要求するか。

この問いを [Extensibility question v2](extensibility-question-v2.md) で開始する。拡張の入力は単なる monoid や monad ではなく、[Base semantic package v2](base-semantic-package-v2.md) で定める構造の束である。

最初の比較基準は [Unordered/deep baseline v2](unordered-deep-baseline-v2.md) の STLC、unordered free-effect rows、exhaustive deep handlers である。ここから base language を段階的に一般化し、[Extension audit v2](extension-audit-v2.md) に従って保存性を検査する。

一般定理を先に仮定せず、共通構文を固定して Writer、State、Exception
を個別に検証した。その共通部分から抽出した現在の結果が [Main
extension theorem v3](main-extension-theorem-v3.md) であり、詳細な証明依存は
[Main extension proof v3](main-extension-proof-v3.md)、反例と限界は [Main
theorem boundaries v3](main-theorem-boundaries-v3.md) にある。recursion 下の
adequacy 条件は [Recursive base adequacy package
v2](recursive-base-adequacy-package-v2.md) に分離した。

```{mermaid}
flowchart LR
  B["Base semantic package"] --> E["Free-operation extension"]
  E --> H1["one-shot handlers"]
  E --> H2["deep one-resumption handlers"]
  E --> H3["multi-shot handlers"]
  B --> P["preserved properties"]
  H1 --> P
  H2 --> P
  H3 --> P
  P --> C["required assumptions / counterexamples"]
```

## 保存する以前の研究線

[Research synthesis v1](research-synthesis-v1.md) 以下の ordered trace、first-actual-head shallow handler、quantitative catch の開発は、現在の主 calculus ではなく次の役割を持つ。

- unordered row が忘れる順序・回数・must/may情報の比較対象
- arbitrary opaque graded monad を直接 inspect できないという境界事例
- base-effectful handler の grade を求める際に trace refinement が必要になる証拠
- shallow、catch-once、deep の handler fragments の比較対象

したがって旧線は **previous ordered/shallow exploration** として凍結し、反例と定理を再利用する。

## 出発点

ベース effect の添字を preordered monoid $(B,\cdot,I,\leq)$ とし、計算を graded monad で解釈する。

$$
S_b X \qquad T_b X \qquad (b\in B)
$$

ここで $S$ は operational model、$T$ は denotational model の候補である。両者が同じ圏上にあるとは仮定しない。最初から関数 $S\to T$ を要求するのではなく、morphism、simulation、logical relation のいずれが適切かを調べる。

開発は [Staged development](staged-development.md) に従う。現在の構文上の基準言語は、free operationsもhandlersもまだ持たない [Base calculus v1](base-calculus-v1.md) である。

ここまでの旧構成、保存できた性質、本質的な限界は
[Research synthesis v1](research-synthesis-v1.md) にまとめてある。

[Exact-layer calculus v2](exact-layer-calculus-v2.md) のfree-product indexはStage 1以降で再検査するproposalであり、現在のbase calculusの定義には含めない。

## 以前の中心的な研究課題

free effect interface $\Delta$ を追加する操作を $\mathsf{Sh}_\Delta$ と仮称する。

$$
S \mapsto \mathsf{Sh}_\Delta S,
\qquad
T \mapsto \mathsf{Sh}_\Delta T.
$$

調べたいのは、対象だけでなく対応も持ち上がるかである。

$$
q:S\Rightarrow T
\quad\mapsto\quad
\mathsf{Sh}_\Delta q:
\mathsf{Sh}_\Delta S\Rightarrow\mathsf{Sh}_\Delta T
$$

$$
R:S\rightsquigarrow T
\quad\mapsto\quad
\mathsf{Sh}_\Delta R:
\mathsf{Sh}_\Delta S\rightsquigarrow\mathsf{Sh}_\Delta T.
$$

これが成立するとして、さらに以下を問う。

- graded monad laws と subeffecting coherence は保存されるか
- shallow handler は持ち上げられた対応に関して compatible か
- graph relation と morphism lifting は一致するか
- base relation の observation/return reflection は保存されるか
- そこから拡張言語の fundamental lemma と adequacy が得られるか

## 現在の主定理から分離するもの

- effect index を一般の圏にすること自体
- proof-relevant な subeffecting
- productive infinite trace を保持する Level-3 adequacy
- occurrence count と precise old base grade
- 動的 effect instance
- 最初から最大一般の基礎圏で定理を書くこと

general recursion と deep handler の再帰的不動点は現在の v3 主定理に含まれる。
上記は主定理の optional refinement または将来拡張として残す。

## 以前の研究線での結論

当初の「任意のgraded monadを直接拡張する」という強い形は一般には成立しない。opaqueな$T$はreturn/operation head decompositionを持たないためである。

現在の肯定的な結論は、free interaction treeによるintensional refinementとtyped foldを組み合わせる形である。この構成はbase conservativity、graded structure、recursion-free adequacy、morphism、logical relationを保存し、exhaustive first-actual-head shallow handlerを自然に持つ。正確な定理と境界は [Research synthesis v1](research-synthesis-v1.md) を参照する。
