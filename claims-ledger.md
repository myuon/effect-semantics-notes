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
| C-034 | Derived | unrestricted tail clause $K(X)\to C$ はbare-value return clause $X\to C$ より強く、base/tail effectsを観測・変更できる | writer counterexample | standard handlerをcanonical lifted tail clausesとして定義できる条件を同定 |
| C-035 | Established | Operational coreではmatching free operationをshallowにeliminateし、base operationをforwardし、return到達時だけbare-value return clauseを実行する | Operational calculus v1 reduction rules | unannotated preservationとdeterminismを証明 |
| C-036 | Adopted definition | 研究はbase calculus、free-operation extension、shallow-handler extension、denotational reconstructionの順に進める | Staged development | Stage 0のB-001--B-003を証明 |
| C-037 | Adopted definition | Stage 0のbase operation syntaxはcontinuationを含むnodeではなく、単純なcomputation $\beta(V):R_\beta!|\beta|$ である | Base calculus v1 | contextual request decompositionを証明 |
| C-038 | Literature theorem | CCC、全射に対するparameterized fixed points、binary coproductsは非退化な一つの圏では共存しない | Huwig–Poigné 1990 | value/computation分離を使ったrecursion semanticsを設計 |
| C-039 | Candidate | Stage 0 calculusはsubeffect coercionsとstrengthを備えた$B$-graded monadで解釈できる | Base denotational semantics v1 | substitution、reduction soundness、coherenceを証明 |
| C-040 | Derived | Stage 0 calculusはsubstitution、internal preservation、deterministic decomposition modulo base requestsを満たす | Base metatheory v1 | mechanization前に規則変更時の再検査を継続 |
| C-041 | Derived conditional | strong graded monad lawsとsubeffect coherenceの下でinternal reductionはdenotational equalityを保存する | Base metatheory v1; C-039 | concrete Writer machineとのadequacyを証明 |
| C-042 | Derived conditional | recursion-free Writer instanceは停止し、ordered logとground Boolについてdenotationがmachine evaluationにadequateである | Writer reducibility; Writer denotation; Base metatheory v1 | reducibility proofを完全展開または形式化 |
| C-043 | Derived | Writer pure grade $1$ はempty operational logを反映し、graded bindはoperational log concatenationと一致する | C-042; Writer graded multiplication | free-operation extensionでの保存条件を抽出 |
| C-044 | Conjecture | machine/denotation/relation/adequacy packageはfree operationsとmatching shallow handlersの追加に沿って持ち上がる | WP-1--WP-8; exact extension definition | Stage 1でoperation-only liftingを定義 |
| C-045 | Candidate | exact free skeleton上のcarrierはskip branchなしの $\widehat T_{b\Delta E}X=T_b(\mathsf{Op}_\Delta(\widehat T_EX))$ でgraded monadを成す | base strong graded monad; polynomial functoriality | bind lawsとstrengthを完全な図式で証明 |
| C-046 | Derived conditional | exact free-operation extensionはStage 0のsubstitution、type safety、deterministic decomposition、base conservativityを保存する | no insertion/deletion of free tokens | labelled machine preservationを完全展開 |
| C-047 | Derived conditional | recursion-free Writer adequacyはexact free interaction treeとのadequacyへ持ち上がる | C-042; C-045; exact-effect inversion | word-length inductionを完全展開 |
| C-048 | Derived | optional free-operation pathを同一gradeで型付けするにはpadding/weakening/explicit boundaryのいずれかが追加で必要である | exact skeleton preorder | Stage 2前にoptional layerを採用するか決定 |
| C-049 | Candidate | $1\to\Delta$ をproof-relevant padding morphismとして加えるとoptional layerは $\mathsf{Layer}_\Delta Z=Z+\mathsf{Op}_\Delta Z$ で解釈できる | word-embedding grading category | categorical compositionとbind naturalityを証明 |
| C-050 | Derived | proof-irrelevantな自由paddingでは $\Delta\to\Delta\Delta$ の挿入位置が複数あり、one-layer handlersがそれらを区別しうる | `skip;op` vs `op;skip` | proof relevanceまたはcanonical elaborationを選択 |
| C-051 | Candidate | matching shallow、unmatched-searching forwarding、final returnを分離したhandler policyがoptional upper-bound layersと整合する | C-049; explicit forwarding semantics | Stage 2 operational rulesを定義 |
| C-052 | Established from source | Original Definition 21はcoercion $be\leq b\Delta e$ とvalue equationを要求しており、free tokenをexact occurrenceではなくoptional upper boundとして扱う | supplied thesis excerpt | operational reconstructionで $(c_{\mathsf{val}})^\sharp$ を導出 |
| C-053 | Question | Original value lifting $T_{be}A\to T_{be'e}C$ はordinary bindではなくlayer-local effect insertionを要求する | effect order in Definition 21 | concrete operational examplesで妥当なorderを決定 |
| C-054 | Derived conditional | left-to-right CBV searching handlerではpadded no-operation pathのeffect orderは $bee'$ だが、matching pathは $be'e$ になる | Optional handler tests P-002--P-005 | common upper boundまたはpositional semanticsを選択 |
| C-055 | Derived | continuationの無視・複製によりtail effectの使用回数が変わるため、固定出力 $be'e$ にはaffinity/idempotence/usage-sensitive typingのいずれかが必要である | P-006--P-007 | handler continuation disciplineを選択 |
| C-056 | Derived | repeated paddingのproof relevanceはhandler styleに依存し、positional handlerはpadding位置を観測するがsearching handlerはquotientできる可能性がある | P-010 | main handler philosophyを選択 |
| C-057 | Adopted reconstruction | Core shallow matcherのmatching branchはoperation resultを生成し、captured continuationを暗黙にexactly once再開し、同じhandlerを再設置しない | clarified source-language intent | formal typing/reduction ruleをStage 2 calculusへ統合 |
| C-058 | Adopted reconstruction | Core matcherのvalue/unmatched behaviorはeffectful return clauseではなくimplicit identity fallbackである | clarified `_ -> y` syntax | unmatched forwardingのhead-form ruleを型付け |
| C-059 | Derived conditional | $1\leq e'$ の下でno-match path $be$ とmatching path $be'e$ は共通upper bound $be'e$ を持つ | optional effect insertion; C-057--C-058 | padding coherenceまたはtrace-bound semanticsを構成 |
| C-060 | Adopted definition | Core shallow matcherはscrutineeの最初のvalue/free-request headを一度だけ検査し、matching・value・unmatchedの全ケースでhandlerを再設置しない | clarified shallowness intent | formal Stage 2 evaluation-context rulesを固定 |
| C-061 | Adopted definition | Stage 2 matcherはinternal step中だけscrutineeを評価し、return/matching free request/unmatched free requestのいずれかを一度処理した時点で消滅する | Shallow matcher calculus v1 | deterministic decompositionを証明 |
| C-062 | Adopted definition | Base requestはfree matcherの判定対象ではなく、base machineが応答した後も同じmatcherがscrutinee評価を継続する | combined base-machine semantics | Writer machineとの合成遷移系を定義 |
| C-063 | Derived conditional | branch effect $e'$ がoptional ($1\leq e'$) ならmatching path $be'e$ とno-match path $be$ はhandler output $be'e$ で統一できる | T-Handle-1; monotonicity | residual-effect context lemmaを証明 |
| C-064 | Proof obligation | T-Handle-1のpreservationには、exposed requestの評価文脈からprefix/request/tail factorizationを復元するtyped context inversion lemmaが必要である | Stage 2 context typing | lemmaを定式化して帰納証明 |
| C-065 | Derived | residual context judgment $\Gamma\vdash\mathcal E:R\xRightarrow{e}A$ はreturned-value pluggingとgeneral computation pluggingを満たす | CT-Hole; CT-Let; T-Let | mechanization時にcontext binderを形式化 |
| C-066 | Derived | exposed request $\mathcal E[\operatorname{op}_\Gamma(V)]$ のprincipal residual effectは $\Gamma e$ にfactorできる | C-065; typing inversion | subeffect derivationを含む完全なinversionを形式化 |
| C-067 | Derived | matching shallow stepのresidual effect orderはbranch $e'$ の後にcaptured tail $e$ が続く $e'e$ である | substitution; C-065--C-066 | denotational handler equationと照合 |
| C-068 | Derived | partial matcherがunmatched operationをforwardする場合、そのoperation tokenはoutput effectから消去できない | R-Handle-Forward; C-066 | trace-language/row-transformerの候補を比較 |
| C-069 | Rejected | partial matcher一般に対して単純なword rule $b\Delta e\mapsto be'e$ を使える | unmatched operation counterexample | exhaustive interface eliminatorに制限、またはgradeを拡張 |
| C-070 | Derived conditional | $\Delta$ の全operationに共通effect $e'$ のbranchがあり $1\leq e'$ ならexhaustive handlerは $b\Delta e\mapsto be'e$ で型付けできる | C-065--C-067; optional branch effects | full preservation theoremを記述 |
| C-071 | Adopted definition | Coreの$\Delta$-indexed handlerは$\Delta$に属する全operationを重複なくbranchとして持つ | C-068--C-070; T-Handler-WF | preservation proofでinversionを使用 |
| C-072 | Deferred extension | Partial operation matcherはcoreに含めず、operation-granular indexまたはtrace transformerを導入する将来拡張として扱う | C-068--C-069 | main denotation完成後に再評価 |
| C-073 | Literature observation | KokaとEffektはeffect/interface handlerを全operationを含む実装単位として扱い、coreのexhaustiveness仮定に近い | official Koka/Effekt documentation | formal rulesとの細部比較を継続 |
| C-074 | Literature observation | OCaml 5はpartial pattern handlerとouter forwardingを許すが、effect safetyを静的には保証しない | OCaml 5 manual | shallow APIのlabelled semanticsを比較 |
| C-075 | Derived taxonomy | 他interfaceをambient rowへforwardすることと、同一interface内の一部operationだけをeliminateすることは異なる | Handler exhaustiveness survey; C-068 | future partial extensionでsignature subtractionを検討 |
| C-076 | Adopted definition | Labelled suspension $M\Uparrow\alpha(V;K)$ はoperation response後のresidual computationをmetalevel continuationとして保持する | Stage 2 operational metatheory v1 | denotational operation treeと対応付け |
| C-077 | Derived | Base suspensionはpending handlerをresponse continuationに保持するが、unmatched free suspensionはhandlerなしのcontinuationをforwardする | S-Handle-Base; S-Handle-Free-Other | nested-handler denotationで自然性を確認 |
| C-078 | Derived | Exhaustive clause uniquenessとraw request decompositionの下でStage 2 one-step semanticsはdeterministic base machineに対して相対的に決定的である | OS-001--OS-003 | mechanization時にmetalevel continuation equalityを表現 |
| C-079 | Derived conditional | Stage 2 suspension propagationはresidual-context typingに関してlabelled preservationを満たす | C-065--C-070; typed machine responses | accumulated trace configurationを完全定義 |
| C-080 | Milestone | Recursion-free Stage 2 coreのoperational designはnested handlersを含めて固定され、denotational validationへ進める | C-057--C-079 | handler denotationを構成 |
| C-081 | Derived conditional | Optional-layer carrierが存在すればlocal handler algebraはskip上のweakeningとoperation上のclause-then-tail bindで定義できる | extended graded monad; $1\leq e'$; exhaustive clauses | optional-layer constructionから仮定を導出 |
| C-082 | Derived conditional | $H_\Delta^{b,e,e'}=T_b(h_{\Delta,e,e'})$ は型 $\widehat T_{b\Delta e}A\to\widehat T_{be'e}A$ を持つ | C-081; carrier isomorphism | base prefix identificationをdiagram化 |
| C-083 | Derived conditional | Handler equationはskipでidentity weakening、operationで$c_{\operatorname{op}}(p)\mathbin{\mathsf{bind}}k$となり、後者に$H_\Delta$の再帰出現がないためshallowである | C-081--C-082 | operational soundness inductionへ統合 |
| C-084 | Derived conditional | Exhaustivenessは$\mathsf{Op}_\Delta$の全coproduct summandから共通codomainへのmapを定義するために十分であり、partial clauseには追加のforwarding summandが必要である | coproduct universal property; C-068 | categorical statementを精密化 |
| C-085 | Milestone | Handler denotation自体はoptional-layer structureからcanonicalに構成でき、主要未解決点は$\widehat T$とcoherent paddingの一般構成へ縮約された | C-081--C-084 | extended graded monad constructionを開始 |

## 証明完了の基準

各 claim は最低限、次を持って初めて **Derived** とする。

- 全ての対象と射の型
- 使用した仮定の明示
- 等式なら可換図式または要素計算
- effect word の結合・subeffecting との整合性
- 境界例（空 interface、pure grade、空 tail）

文献に同様の定理があるだけでは、この台帳上の claim は Established/Derived にならない。
