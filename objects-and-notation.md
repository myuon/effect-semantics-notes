# Objects and notation

## Base effects

**Candidate.** Base effects は preordered monoid $(B,\cdot,I,\leq)$ とする。

- $I$: pure effect
- $b\cdot c$: evaluation orderを保つ逐次合成
- $b\leq c$: proof-irrelevant な subeffecting

通常の subeffecting が目的なら preorder で十分と予想する。平行射を持つ category grading は、effect translation や handler を同じ射として符号化する場合に再検討する。

## Base graded monad

基礎圏 $\mathcal C$ 上で、各 $b\in B$ に自己関手 $T_b$ を持ち、

$$
\eta_X:X\to T_I X,
\qquad
\mu_{b,c,X}:T_bT_cX\to T_{b\cdot c}X
$$

および subeffect coercion

$$
\tau_{b,c,X}:T_bX\to T_cX \quad (b\le c)
$$

を持つものを考える。必要な strength、余積、指数対象は構成を確定した時点で列挙する。

## Free effect interfaces

interface $\Delta$ は operation の族

$$
\operatorname{op}_i:A_i\to B_i
$$

からなる。ここで $A_i$ は parameter type、$B_i$ は operation result type。

一層の operation shape の候補は

$$
\mathsf{Op}_\Delta X
=
\coprod_i A_i\times X^{B_i}.
$$

return/tail branch を含めた polynomial は

$$
P_\Delta X = X + \mathsf{Op}_\Delta X.
$$

## Extended effect words

**Working definition.** Base-effect monoidを $B$、interfaces上のfree monoidを $\mathcal D^*$ とし、拡張effect monoidをfree product

$$
\widehat E=B*\mathcal D^*
$$

とする。reduced normal formは base effects と nonempty free-operation words の有限交互列である。細粒度表記では

$$
b_0\,\Delta_1\,b_1\cdots\Delta_n\,b_n
$$

で表す。交換則は置かず、順序を意味論的layer structureとして保存する。

未決定事項:

- 空の base segment/interface を正規形から除くか
- free productをreduced wordsとして実装するか、coproductの普遍性から抽象的に扱うか
- componentwise subeffecting 以外の weakening を許すか
- 同一 interface の反復をまとめるか区別するか

## Correspondences between models

三段階を区別する。

1. **Strict/function-like:** graded monad morphism $q:S\Rightarrow T$
2. **Relational:** graded simulation / relator $R:S\rightsquigarrow T$
3. **Observational:** TT-lifting または biorthogonality による relation

strict case は relational case の graph として埋め込める可能性がある。
