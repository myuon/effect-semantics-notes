# Claims ledger

主張には安定したIDを付ける。証明、反例、仮定変更はこのページから追跡する。

| ID | Status | Claim | Dependencies | Next check |
|---|---|---|---|---|
| C-001 | Candidate | Base effect index は preordered monoid で十分である | 通常の subeffecting が proof-irrelevant | handler/translation を index morphism に含める必要がないか確認 |
| C-002 | Conjecture | finite shallow-layer construction は extended effect words 上の graded monad を与える | exact definition of words; categorical structure | unit/bind を完全に定義して三法則を計算 |
| C-003 | Conjecture | shallow extension は graded monad morphisms を持ち上げる | C-002; preservation of polynomial structure | $\widehat q$ を定義し unit/bind naturality を確認 |
| C-004 | Conjecture | shallow extension は graded simulations/logical relations を持ち上げる | base relator laws; layer relation | bind compatibility を証明 |
| C-005 | Conjecture | graph lifting は morphism lifting の graph と一致する | C-003; C-004 | effect-word induction |
| C-006 | Conjecture | relational clauses を満たす operational/denotational handlers は拡張 relation を保存する | C-004; exact handler typing | shallow case analysisを展開 |
| C-007 | Conjecture | base relation が ground returns を反映すれば、extended relation も反映する | coproduct separation; base observation | operation branch が return と混同されない条件を同定 |
| C-008 | Conjecture | fundamental lemma と C-007 から adequacy preservation が従う | calculus and typing rules; C-006 | observation statementを固定 |
| C-009 | Question | morphism theorem は relational theorem の特殊例として完全に回収できるか | graph compatibility | strength/subeffect coherence を含めて比較 |
| C-010 | Question | finite shallow layers は既存の higher-order/scoped-effect framework の特殊例か | precise literature comparison | 文献の定義と1対1対応を作る |
| C-011 | Derived | 標準的 shallow handler の operation clause に渡る continuation は同じ handler で再処理されない | Minimal calculus v0 の reduction rule | 文献上の標準定義と照合 |
| C-012 | Derived | Candidate A の tail branch と標準的 shallow return clause は、そのままでは型が一致しない | Candidate A; Minimal calculus v0 | 元の修論の handler rule を復元して分岐を解消 |
| C-013 | Conjecture | 精密な shallow-handler effect rule は continuation の利用方法を反映する必要がある | continuation may be ignored/duplicated/invoked | effect variables または handler effect transformer を設計 |
| C-014 | Established | Baseline v1 では effect annotations を非可換 preordered monoid の上界として読む | adopted language definition | semantic coherence を証明 |
| C-015 | Derived | `R-Let-Op` の両辺の effect は monoid associativity により一致する | T-Let; T-Op | 完全な preservation proof に組み込む |
| C-016 | Conjecture | Baseline v1 は preservation と progress modulo exposed operations を満たす | substitution; effect coherence | M-001–M-005 を紙上で証明 |
| C-017 | Question | word-layer construction は v1 の handler-under-base-prefix を実装するか | head-normal semantics; layer semantics | 両意味論を定義して比較図式を作る |
| C-018 | Derived | graded monad と primitive operations は explicit operation nodes を解釈できる | graded bind; $\mathsf{op}^T:P\to T_{[\Delta]}R$ | substitution semantics に組み込む |
| C-019 | Derived | `R-Let-Op` の soundness は graded bind associativity から従う | C-018 | formal commuting diagram を追加 |
| C-020 | Derived | arbitrary graded monad + primitive operations だけでは syntax-directed shallow handler を一様に定義できない | collapsed one-point model | categorical non-definability statement に精密化 |
| C-021 | Rejected | Baseline v1 as written が unrestricted subeffecting の下で progress modulo operations を満たす | mismatched exposed operation counterexample | forwarding または head refinement を追加 |
| C-022 | Candidate | effect upper bound と observable head shape を別 index にする | C-020; C-021 | row+forwarding calculus と比較 |
| C-023 | Derived | head-shape composition $s\blacktriangleright t$ は結合的で $\{\checkmark\}$ を単位元に持つ | case analysis on return membership | algebraic proofを補題化 |
| C-024 | Derived | head shapes は subset ordering の下で noncommutative preordered monoid を成す | C-023; monotonicity | counterexampleで非可換性を明示 |
| C-025 | Derived | simple head shapes は handler progress を保証できるが residual continuation の型を復元できない | refined handler typing attempt | residual-aware shapeを定義 |
| C-026 | Conjecture | residual-aware head shape は free shallow layer の polynomial presentation と一致する | C-025; Candidate A | representation/isomorphismを構成 |
| C-027 | Derived | rows は `log; ask` と `ask; log` を区別しないが head shapes は区別する | P-002; P-003 | operational correspondenceを定式化 |
| C-028 | Established | Main lineのextended effect monoidは $B*\mathcal D^*$ であり、indexはupper boundではなくlayer structureを表す | Exact-layer calculus v2 | normal-form theoremを証明 |
| C-029 | Established | Shallow handlerはoperation type $\Delta$ でindexされ、matching exposed $\Delta$-layerだけをprimitiveにeliminateする | Exact-layer calculus v2 | clause effectsを確定 |
| C-030 | Rejected | 独立したhead-shape indexをmain calculusに追加する | typed free layer already carries full head data | abstractionとしてのみ保存 |
| C-031 | Conjecture | matching handlerはouter base segmentを通してcanonicalにliftできる | base functoriality/strength/algebra laws | exact lifting diagramを定義 |
| C-032 | Question | free-layer return branchは $X$ かtail carrier $K$ か | original typing/evaluation intent | unitとbindの型から判定 |
| C-033 | Derived (conditional) | exact layerをskipした後のeffectful sequencingを許すなら、free-layerの左branchはbare $X$ ではなくtail computation $K$ を収容する必要がある | ordinary effectful bind; no canonical $K(Y)\to Y$ | $K+\mathsf{Op}_\Delta(K)$ 上のbindを定義 |

## 証明完了の基準

各 claim は最低限、次を持って初めて **Derived** とする。

- 全ての対象と射の型
- 使用した仮定の明示
- 等式なら可換図式または要素計算
- effect word の結合・subeffecting との整合性
- 境界例（空 interface、pure grade、空 tail）

文献に同様の定理があるだけでは、この台帳上の claim は Established/Derived にならない。
