# Candidate constructions

このページの式はまだ採用済みの定義ではない。型が通るか、monad laws が成立するか、元の calculus の意図と一致するかを順に検査する。標準的な比較対象は [Minimal calculus v0](minimal-calculus-v0.md) に置いた。

> **Known mismatch:** Candidate A の value branch は tail computation を含むが、標準的 shallow handler の return clause は値を受け取る。両者を同一視してはならない。

## Candidate A: finite shallow layers

extended word の長さに関して再帰的に、

$$
\widehat T_b X = T_bX
$$

および

$$
\widehat T_{b\Delta e}X
=
T_b\left(
  \widehat T_eX
  \coprod_{\operatorname{op}_i:A_i\to B_i\in\Delta}
  A_i\times( B_i\Rightarrow\widehat T_eX)
\right)
$$

と置く。

**Status: Candidate / semantic intention unresolved.** これは標準的な head-normal shallow tree ではなく、effect word 内の指定された layer を分解する構成である可能性が高い。

直観:

- 外側の $T_b$ は、次の未処理 free operation に到達するまでの base computation
- 左の branch は、free operation を起こさず tail に進んだ計算
- 右の branch は、先頭の未処理 operation と shallow continuation
- continuation は handler に渡されるが、その handler で再帰的に処理されない

### 直ちに検査すべき点

1. 式中の $A_i,B_i$ は基礎圏の対象か、構文型の解釈か。
2. $T_b$ が必要な coproduct/exponential をどう扱うか。
3. extended bind をどのように定義するか。
4. bind が free layer をまたぐとき effect word がどう結合されるか。
5. associativity が definitional か、canonical isomorphism を介するか。
6. subeffect coercion をどの構造から得るか。

## Layer-handler candidate

この構成に対応する layer eliminator の value/tail clause と operation clauses を

$$
h_{\mathrm{tail}}:\widehat T_eX\to\widehat T_{e'}Y
$$

$$
h_i:A_i\times(B_i\Rightarrow\widehat T_eX)
\to\widehat T_{e'e}Y
$$

と仮定するのが型として自然である。一層の case analysis

$$
[h_{\mathrm{tail}},\coprod_i h_i]
$$

を $T_b$ の下で作用させ、graded multiplication で平坦化することで

$$
H^T_\Delta:
\widehat T_{b\Delta e}X
\to
\widehat T_{be'e}Y
$$

を得る案。

**Question.** この layer eliminator は元の shallow handler と同じ操作なのか、それとも別の、effect boundary を操作する構文なのか。

## Relation lifting candidate

base に左右の graded monads $S,T$ と relation lifting

$$
\overline{S,T}_b(R)
\subseteq S_bX\times T_bY
$$

があるとする。free layer では同一 branch のみを関連づける。

Operation branch では parameter を値関係で、continuation を pointwise な計算関係で関連づける。概略、

$$
\widehat R_{b\Delta e}
=
\overline{S,T}_b\bigl(\mathsf{Layer}_{\Delta}(\widehat R_e)\bigr).
$$

この定義から unit、bind、subeffecting、handler compatibility、return reflection のどれが自動的に従い、どれが追加仮定を要するかを分解する。

## Alternative B: recursive/free-monad construction

$$
MX\cong T(X+H_\Delta MX)
$$

の初期代数や自由モナドで全ての operation tree を一度に作る案。

これは deep handlers や任意深さの tree には自然だが、現在の shallow-extension theorem には強すぎる可能性がある。Candidate A と同じ対象を別表示しているのか、異なる calculus を意味するのかを明確にする。
