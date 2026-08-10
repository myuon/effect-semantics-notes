# Semantic interface v1

## Status

**Working analysis.** このページでは Baseline calculus v1 を解釈するために、graded monad に何を追加する必要があるかを分解する。

## 1. Base graded semantics

基礎圏を $mathcal C$、effect algebra を preordered monoid

$$
(E,\cdot,1,\leq)
$$

とする。まず strong graded monad の族

$$
T_e:\mathcal C\to\mathcal C
$$

を仮定する。構造写像は

$$
\eta_X:X\to T_1 X,
$$

$$
\mu_{e,f,X}:T_eT_fX\to T_{e\cdot f}X,
$$

および subeffecting に対する coherent coercion

$$
\tau_{e,f,X}:T_eX\to T_fX
\qquad(e\leq f)
$$

である。

この構造だけで `return`、`let`、application、subeffecting は解釈できる。

## 2. Primitive operations

$\operatorname{op}:P\to R\in\Delta$ に対し、primitive operation を

$$
\mathsf{op}^T:P\to T_{[\Delta]}R
$$

として与える。

すると explicit operation node

$$
\operatorname{op}(V;y.M)
$$

は、parameter の解釈 $p:P$ と continuation

$$
k:R\to T_eX
$$

から

$$
P
\xrightarrow{\mathsf{op}^T}
T_{[\Delta]}R
\xrightarrow{T_{[\Delta]}k}
T_{[\Delta]}T_eX
\xrightarrow{\mu_{[\Delta],e}}
T_{[\Delta]\cdot e}X
$$

と解釈できる。

したがって、graded monad と primitive operations があれば `T-Op` の意味は与えられる。

## 3. Sequencing soundness

`R-Let-Op` の左辺は

$$
(\mathsf{op}^T(p)\mathbin{\mathsf{bind}}k)
\mathbin{\mathsf{bind}}h,
$$

右辺は

$$
\mathsf{op}^T(p)
\mathbin{\mathsf{bind}}
(\lambda r.k(r)\mathbin{\mathsf{bind}}h)
$$

と解釈される。両者の等しさは graded bind の結合律そのものである。

**Derived conclusion.** `R-Let-Op` の soundness は operation 固有の代数則ではなく graded monad associativity から従う。

## 4. Why handlers need more structure

Handler reduction `R-Handle-Op` は、入力計算の先頭が

- return
- $\Delta$ の operation

のどちらかを識別し、operation の parameter と continuation を取り出す。

しかし、一般の carrier

$$
T_{[\Delta]\cdot e}X
$$

には、そのような分解写像は存在しない。graded monad の unit と multiplication は計算を**構成・合成**するが、構成済みの計算を return/operation に**分解**しない。

Primitive map

$$
\mathsf{op}^T:P\to T_{[\Delta]}R
$$

も operation を carrier に埋め込むだけであり、その像から parameter と continuation を回収する方法を与えない。

## 5. Non-definability test

極端なモデルとして、全ての effects と values を一点へ潰す graded monad を考える。

$$
T_eX=1.
$$

unit、multiplication、primitive operations は一意に存在する。しかし carrier 内では

$$
\mathsf{return}\;x
$$

と

$$
\operatorname{op}(p;k)
$$

の像を区別できない。

return clause と operation clause が異なる結果を返す handler は、このモデル上で入力の head form に従って選択できない。

**Derived conclusion.** arbitrary graded monad + primitive operations から、syntax-directed な shallow handler を一様には定義できない。

これはそのモデルが adequacy を満たさないというだけではない。handler の denotation 自体を、指定された二つの reduction equations を満たす形で定義する材料が不足している。

## 6. Required decomposition

標準的な shallow handler に直接対応する head functor を

$$
\mathsf{Op}_\Delta Z
=
\coprod_{\operatorname{op}:P\to R\in\Delta}
P\times Z^R
$$

とする。

先頭形を保存する carrier の候補は

$$
\mathsf{Head}_{\Delta,e}(X)
=
X+\mathsf{Op}_\Delta(T_eX).
$$

要素的には

$$
\mathsf{return}(x)
$$

または

$$
\mathsf{op}(p,k),
\qquad k:R\to T_eX
$$

である。

Handler clauses

$$
h_r:X\to T_fC
$$

and

$$
h_{\operatorname{op}}:
P\times(T_eX)^R\to T_fC
$$

があれば、coproduct elimination により

$$
[h_r,\coprod h_{\operatorname{op}}]:
\mathsf{Head}_{\Delta,e}(X)\to T_fC
$$

を得る。これは shallow case analysis の意味論そのものである。

## 7. Two possible semantic architectures

### Architecture A — Free/head-preserving model

Extended operational/denotational carrier を、head form が構造として残る free construction で作る。

$$
\mathsf{Head}_{\Delta,e}(X)
=X+\mathsf{Op}_\Delta(T_eX).
$$

利点:

- shallow handler は単なる case analysis
- return と operation の分離が明示的
- logical relation を coproduct/積/指数から構造的に持ち上げられる

課題:

- tail-only computation $T_eX$ をどう埋め込むか
- sequential composition で head structure がどう変化するか
- subeffecting と「operation が起きない」計算の扱い

### Architecture B — Abstract model with a reification law

一般の graded monad $T$ に追加構造として decomposition

$$
\mathsf{out}_{\Delta,e,X}:
T_{[\Delta]\cdot e}X
\to
X+\mathsf{Op}_\Delta(T_eX)
$$

を要求する。

少なくとも

$$
\mathsf{out}(\eta x)=\mathsf{inl}(x)
$$

と

$$
\mathsf{out}(\mathsf{op}(p)\mathbin{\mathsf{bind}}k)
=
\mathsf{inr}(\mathsf{op},p,k)
$$

に相当する equations が必要である。

利点:

- handler を既存 carrier 上に定義できる

課題:

- 非常に強い仮定であり、どのモデルが満たすか不明
- general base effects や quotient models では head information が失われうる
- $\mathsf{out}$ が自然か、inverse/congruenceを持つかを決める必要がある

## 8. A newly exposed typing problem

Baseline v1 は effect annotations を上界として読む。一方、handler rule は

$$
M:A!([\Delta]\cdot e)
$$

から、実行時 head form が return または $\Delta$-operation であることを期待する。

しかし unrestricted subeffecting が

$$
g\leq[\Delta]\cdot e
$$

を許す場合、$M$ は別 interface の exposed operation を持つ可能性がある。そのとき現行の reduction rules には

- matching clause
- forwarding rule

のどちらもない。

したがって Baseline v1 の progress claim は、現状のままでは証明できない。

## 9. Repair options for the calculus

### Repair 1 — Separate head shape from effect upper bound

Judgment に head specification を追加する。

$$
\Gamma\vdash M:A!e\;\triangleright\;s
$$

ここで $s$ は `return-or-$\Delta$` のような shape を表す。handler は effect ではなく shape を根拠に型付けする。

### Repair 2 — Use effect rows and forwarding

標準的 handler calculus のように、入力 effect row から $\Delta$ を除き、それ以外の operation を forwarding する。

これは標準的だが、非可換な sequential effects という当初の関心から離れる可能性がある。

### Repair 3 — Make the layer explicit in syntax/types

通常の computation と別に

$$
\mathsf{Layer}_\Delta(e,A)
$$

のような型を導入し、constructor と eliminator を明示する。以前の Candidate A はこの方向に近い。

### Repair 4 — Restrict subeffecting around handler boundaries

Handler 入力に canonical derivation または exact leading grade を要求する。最小だが、typing が derivation-sensitive になりやすく、coherence の問題を生む。

## 10. Current recommendation

**Candidate decision.** effect upper bound と observable head shape を分離する Repair 1 を第一候補とする。

理由:

- sequential grade $e\cdot f$ を維持できる
- shallow handler が必要とする分解可能性を型に明示できる
- operational/denotational correspondence の保存対象を effect と shape の二層に分けられる
- layer semantics との関係も記述しやすい

ただし、shape system を新設する前に、Repair 2 の標準的 forwarding calculus と比較し、余計な構造を発明していないか確認する。

## 11. Next calculation

次は二つの小さな体系を並べる。

1. effect rows + forwarding を持つ標準 shallow calculus
2. sequential grades + head shapes を持つ refined calculus

同じ三つのプログラムについて typing と reduction を比較し、研究目的に必要な差だけを抽出する。
