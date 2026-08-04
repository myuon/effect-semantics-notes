# Research map

## 出発点

ベース effect の添字を preordered monoid $(B,\cdot,I,\leq)$ とし、計算を graded monad で解釈する。

$$
S_b X \qquad T_b X \qquad (b\in B)
$$

ここで $S$ は operational model、$T$ は denotational model の候補である。両者が同じ圏上にあるとは仮定しない。最初から関数 $S\to T$ を要求するのではなく、morphism、simulation、logical relation のいずれが適切かを調べる。

構文上の基準言語は [Baseline calculus v1](baseline-calculus-v1.md) とする。これは元の修論の再現ではなく、以後の主張を検査可能にするため固定した working calculus である。

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

## 期待する研究上の貢献（暫定）

**Conjecture.** Shallow free-effect extension は、operational model と denotational model を別々に作り直す操作ではなく、graded semantic structures とその間の strict/relational correspondence に作用する一つの構成として整理できる。

この主張が既存研究の単なる言い換えか、新しい保存定理になるかは、文献調査と正確な定理化の後で判断する。
