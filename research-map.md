# Research map

## 出発点

ベース effect の添字を preordered monoid $(B,\cdot,I,\leq)$ とし、計算を graded monad で解釈する。

$$
S_b X \qquad T_b X \qquad (b\in B)
$$

ここで $S$ は operational model、$T$ は denotational model の候補である。両者が同じ圏上にあるとは仮定しない。最初から関数 $S\to T$ を要求するのではなく、morphism、simulation、logical relation のいずれが適切かを調べる。

開発は [Staged development](staged-development.md) に従う。現在の構文上の基準言語は、free operationsもhandlersもまだ持たない [Base calculus v1](base-calculus-v1.md) である。

ここまでの構成、保存できた性質、本質的な限界、および現在の主張は
[Research synthesis v1](research-synthesis-v1.md) にまとめる。

[Exact-layer calculus v2](exact-layer-calculus-v2.md) のfree-product indexはStage 1以降で再検査するproposalであり、現在のbase calculusの定義には含めない。

## 中心的な研究課題

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

## 今のところ主題にしないもの

- effect index を一般の圏にすること自体
- proof-relevant な subeffecting
- deep handler の再帰的不動点
- general recursion や動的 effect instance
- 最初から最大一般の基礎圏で定理を書くこと

これらを排除したわけではない。中心構成が固まった後の拡張候補として保留する。

## 現在の研究上の結論

当初の「任意のgraded monadを直接拡張する」という強い形は一般には成立しない。opaqueな$T$はreturn/operation head decompositionを持たないためである。

現在の肯定的な結論は、free interaction treeによるintensional refinementとtyped foldを組み合わせる形である。この構成はbase conservativity、graded structure、recursion-free adequacy、morphism、logical relationを保存し、exhaustive first-actual-head shallow handlerを自然に持つ。正確な定理と境界は [Research synthesis v1](research-synthesis-v1.md) を参照する。
