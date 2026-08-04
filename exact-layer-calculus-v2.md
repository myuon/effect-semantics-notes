# Exact-layer calculus v2

## Status

**Adopted as the current working calculus.**

この版では、effect index を通常の「起こりうるeffectsの集合」や上界として読まない。index は base computations と free-operation layers の順序付き構造を記録する。

二つの固定条件は次である。

1. shallow handler は operation type $\Delta$ でindexされ、露出したfree layerのtypeが一致するときだけeliminateする。
2. extended effect index は、base-effect monoidとfree-operation monoidの自由積として構成し、正規形は両者の交互列になる。

## 1. Base effects

Base calculus のeffect algebraをmonoid

$$
(B,\cdot_B,1_B)
$$

とする。

$b\in B$ は既存のbase computation effectを表す。必要なら後からpreorderを加えるが、free-layerの構造を壊す任意のsubeffectingは導入しない。

## 2. Free operation types

Free operation type/interfaceの集合を $\mathcal D$ とする。各

$$
\Delta\in\mathcal D
$$

はoperation signature

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}
\qquad(\operatorname{op}\in\Delta)
$$

を持つ。

Free-operation effectsは $\mathcal D$ 上のfree monoid

$$
\mathcal D^*
$$

を成す。積はoperation-type wordsの連結、単位元は空word $\epsilon$ である。

## 3. Extended effects as a free product

Extended effect monoidを

$$
\widehat E=B*\mathcal D^*
$$

とする。ここで $*$ はmonoidsのfree productである。

この定義の意味は、$B$ 内部の積と $\mathcal D^*$ 内部の連結以外に、base effectsとfree operationsの間の交換則を置かないことである。

### Alternating normal forms

Free productのreduced wordは、概略

$$
b_0\;w_1\;b_1\;w_2\;\cdots\;w_n\;b_n
$$

と表せる。ここで

$$
b_i\in B,
\qquad
w_i\in\mathcal D^+
$$

であり、内部に現れるfactorは単位元ではない。

Free-operation blockをoperation typeごとに露出する細粒度表記では、

$$
b_0\;\Delta_1\;b_1\;\Delta_2\;\cdots\;\Delta_n\;b_n
$$

のような交互列を用いる。この表記では、必要に応じてidentity base segmentを明示して、連続するfree operationsを分離できる。

### No commutation

一般に

$$
b\cdot\Delta\neq\Delta\cdot b.
$$

これは単なる構文上の違いではない。handlerが到達できるfree layerの位置が異なる。

## 4. Meaning of the index

Judgment

$$
\Gamma\vdash M:A!E
\qquad(E\in\widehat E)
$$

における $E$ は、計算のlayer structureを指定する。

たとえば

$$
M:A!(\Delta\cdot b\cdot E)
$$

は、意味論的に最外側にfree $\Delta$-layerがあり、そのcontinuation側にbase effect $b$ とtail $E$ があることを表す。

これは

> $M$ では $\Delta,b,E$ のどれかが起こりうる

というunordered upper boundではない。

## 5. Semantic carrier of one free layer

Tail carrierを

$$
K_{b,E}(X)=T_b(\widehat T_EX)
$$

と略記する。

Interface $\Delta$ のone-operation shape functorを

$$
\mathsf{Op}_\Delta Z
=
\coprod_{\operatorname{op}:P\to R\in\Delta}
P\times Z^R
$$

とする。

最外側のfree layerの第一候補は

$$
\widehat T_{\Delta\cdot b\cdot E}X
=
X+\mathsf{Op}_\Delta(K_{b,E}(X)).
$$

すなわち要素は

$$
\mathsf{return}_\Delta(x)
$$

または

$$
\mathsf{op}_\Delta(p,k),
\qquad
k:R\to T_b(\widehat T_EX)
$$

である。

### Important typing point

左branchは $X$ であり、tail computation $K_{b,E}(X)$ ではない。これはmatching shallow handlerのreturn clauseが値を受け取る設計に対応する。

もし元のcalculusで「そのfree layerをskipしてtail computationを残す」constructorが必要なら、carrierは別途

$$
K_{b,E}(X)+\mathsf{Op}_\Delta(K_{b,E}(X))
$$

とする必要がある。この二案は同一ではないため、後でtyping rulesから決定する。

### A program that separates the two candidates

$\Delta$ に一つのoperation

$$
\mathsf{coin}:1\to\mathsf{Bool}
$$

があり、base calculus に writer operation

$$
\mathsf{tell}:\mathsf{String}\to 1
$$

があるとする。次のプログラムを考える。

```text
if c then
  let x <- perform coin () in
  tell "coin";
  return x
else
  tell "default";
  return false
```

両方の分岐を正確なlayer index $\Delta\cdot b$ で型付けしたい。then branch は

$$
\mathsf{op}_\Delta
  ((),\lambda x.\;\mathsf{tell}\;\text{"coin"};\mathsf{return}\;x)
$$

なので、どちらの候補でも $\mathsf{Op}_\Delta(K_{b,1}(\mathsf{Bool}))$ に入る。

差が出るのは else branch である。このbranchは $\Delta$-operationを起こさないが、tailのbase computation

$$
\mathsf{tell}\;\text{"default"};\mathsf{return}\;\mathsf{false}
\in K_{b,1}(\mathsf{Bool})
$$

を持つ。したがって

$$
K_{b,1}(X)+\mathsf{Op}_\Delta(K_{b,1}(X))
$$

なら左branchにそのまま格納できる。一方、

$$
X+\mathsf{Op}_\Delta(K_{b,1}(X))
$$

の左branchに入るのは bare value $\mathsf{false}$ だけであり、`tell "default"` を表す場所がない。

同じ問題は条件分岐を使わなくても、sequencingだけで現れる。

```text
return_Delta ();
tell "after";
return 42
```

$\mathsf{return}_\Delta(())$ を $f(*)=\mathsf{tell}\;\text{"after"};\mathsf{return}\;42$ と bind すると、結果のno-operation branchは $f(*)\in K$ である。ゆえに、通常のeffectful bindに閉じるためには左branchが $K$ を受け取るか、別途

$$
K(Y)\to Y+\mathsf{Op}_\Delta(K(Y))
$$

に相当する特殊なcollapse/padding構造が必要になる。一般のeffectful $K$ からbare value $Y$ を取り出すcanonical mapはない。

この例から得られる暫定結論は次である。

- exact grade $\Delta\cdot b$ が「$\Delta$ を起こさない経路でも $b$ を実行できる」なら、$K+\mathsf{Op}_\Delta(K)$ が必要である。
- $X+\mathsf{Op}_\Delta(K)$ を選ぶなら、no-operation pathはpure returnに制限され、base effectsはoperation continuation内にしか置けないという非対称なcalculusになる。
- 前者の左branchは標準的shallow handlerのbare-value return clauseとは異なる。そのため、得られるeliminatorをそのまま標準的shallow handlerと呼べるかは別途検討する。

## 6. Typed shallow handlers

A shallow handler is indexed by the operation type it eliminates. To distinguish it from the operation-shape functor, write

$$
\mathcal H_\Delta.
$$

Its clauses are

$$
h_{\mathsf{return}}:X\to C
$$

and, for each $\operatorname{op}:P\to R\in\Delta$,

$$
h_{\operatorname{op}}:
P\times(R\to T_b(\widehat T_EX))
\to C.
$$

By coproduct elimination,

$$
\llbracket \mathcal H_\Delta\rrbracket:
X+\mathsf{Op}_\Delta(T_b(\widehat T_EX))
\to C.
$$

The continuation is passed to the clause unchanged. Hence the handler is shallow.

## 7. Matching elimination rule

The typing rule has the schematic form

$$
\frac{
\Gamma\vdash M:A!(\Delta\cdot b\cdot E)
\qquad
\Gamma\vdash \mathcal H_\Delta:A\Rightarrow C
}
{
\Gamma\vdash
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;\mathcal H_\Delta
:C!F
}.
$$

The exact output effect $F$ is determined by the effects of the clauses and whether they invoke the continuation. It is not fixed yet.

The key structural side condition is exact matching:

$$
\text{handler index }\Delta
=
\text{exposed free-layer type }\Delta.
$$

## 8. Mismatching handlers

If

$$
\Gamma\vdash M:A!(\Delta\cdot b\cdot E)
$$

and $\Gamma_0\neq\Delta$, then

$$
\mathsf{handle}^{\mathsf{sh}}_{\Gamma_0}M
$$

does not receive a typing derivation from the primitive elimination rule.

This is intentional. A handler is not a dynamic search through an unordered effect row; it is the eliminator of a matching typed free layer.

## 9. Handler below a base layer

For a computation with index

$$
b\cdot\Delta\cdot E,
$$

the $\Delta$-layer is not exposed at the outermost position. The primitive handler rule does not immediately apply.

The research question is whether the base semantics admits a canonical lifting

$$
T_b(\widehat T_{\Delta\cdot E}X)
\longrightarrow
T_b(\widehat T_EC)
$$

constructed from functoriality, strength, distributive structure, or an algebra carried by the handler clauses.

This is not ordinary forwarding. It is the structure-preserving extension of a matching eliminator through an existing base effect.

## 10. Why head shapes are no longer primitive

The type

$$
\widehat T_{\Delta\cdot b\cdot E}X
=X+\mathsf{Op}_\Delta(T_b(\widehat T_EX))
$$

already exposes exactly the information that the previous head-shape proposal attempted to approximate:

- return branch
- operation type $\Delta$
- parameter
- typed residual continuation

Therefore no independent head-shape index is needed on the main line. Head shapes remain useful only as an abstraction of this free-layer datatype.

## 11. Subeffecting discipline

Any preorder on $\widehat E$ must preserve the layer information used by elimination.

Safe candidates include:

- monotone change inside a base segment $b\leq_B b'$
- signature inclusion $\Delta\subseteq\Delta'$ together with an explicit injection of free layers
- congruence under surrounding effect words

An arbitrary rule that changes the exposed factor from $\Delta$ to unrelated $\Gamma$ is not coherent with typed handler elimination.

## 12. Immediate proof obligations

1. Prove that $B*\mathcal D^*$ has the claimed alternating normal forms.
2. Fix whether a free layer has carrier $X+\mathsf{Op}_\Delta K$ or $K+\mathsf{Op}_\Delta K$.
3. Define unit and sequential bind on all alternating words.
4. Prove that matching handler equations are well typed.
5. Define lifting of handler elimination through an outer base segment.
6. Lift base-model morphisms and logical relations through the same free-layer polynomial.

## 13. Current central conjecture

Let $S,T$ be base graded models and let

$$
R:S\rightsquigarrow T
$$

be a structure-preserving relation. Extending both models along

$$
B\longrightarrow B*\mathcal D^*
$$

by typed free layers should produce

$$
\widehat R:\widehat S\rightsquigarrow\widehat T
$$

such that matching shallow handlers are related and base observations remain adequate under explicit separation assumptions.
