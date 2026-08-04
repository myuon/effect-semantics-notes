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
| C-086 | Derived obstruction | Middle padding $\widehat T_{be}\to\widehat T_{b\Delta e}$ のnaive layer実装には一般にsplit $T_{be}\to T_bT_e$ が必要で、graded monadが与える$\mu:T_bT_e\to T_{be}$とは逆向きである | optional carrier equation; type calculation | concrete countermodelsとsplit assumptionsを比較 |
| C-087 | Derived | Proof-relevant word embeddingはpadding位置を区別するが、対応するsemantic mapの存在は保証しない | C-050; C-086 | grading categoryとsemantic actionを分離して定義 |
| C-088 | Candidate | Natural sections $\delta_{b,e}:T_{be}\to T_bT_e$ とunit/coassociativity coherenceを仮定すればmiddle paddingを構成できる | C-086; section laws | monad lawsとpadding naturalityを完全計算 |
| C-089 | Candidate | Raw segmented gradesを$T_bT_e$で解釈すればsplitなしにboundary insertionできるが、base $T_{be}$へのconservativityは$\mu$によるlax flatteningになる | segmented-word construction | Writer modelでflattening adequacyを検証 |
| C-090 | Candidate | Free interaction semanticsを先に構成し$T$へ解釈すればarbitrary base modelをtargetとして保てるが、carrier equalityではなくfree refinement theoremになる | interaction-tree construction | segmented Writerとの比較計算 |
| C-091 | Derived | Writerでmiddle paddingを入れることはlogのcutを選ぶことに相当し、左端・右端を含む複数の$\mu_{w,w}$のsectionが存在する | Writer concatenation | split coherenceの一般則と比較 |
| C-092 | Counterexample | Grade $\Delta\Delta$ の一operation programでpositional eliminatorは`op;skip`をhandleし`skip;op`を残すため、padding proofを観測する | repeated-padding Writer test | positional denotationをcore handlerから分離 |
| C-093 | Rejected | Local algebra $h(\mathsf{inl}(z))=z$ がfirst-actual-head source handlerを一般に解釈する | C-092; skip is not final return | skip traversalまたはfree-tree semanticsへ置換 |
| C-094 | Derived | Finite Writer interaction tree上のhandlerはTellにだけ再帰し、matching free nodeでclause bind、other free nodeでidentityとすればdirect operational rulesと一致する | TW-Ret--TW-Other | operational adequacyを帰納証明 |
| C-095 | Preferred candidate | Main denotationはpadding nodeを持たないfree interaction treeをordered trace upper boundsでgradeし、base-only fragmentを$T$へ解釈するrefinementとする | C-086--C-094 | graded tree carrierとWriter adequacyを定義 |
| C-096 | Derived | Downward-closed finite trace languagesはunionをjoin、downward-closed concatenationを積とするunital quantaleを成す | subsequence preorder; word concatenation | general base gradesへの置換を検討 |
| C-097 | Derived | Finite Writer interaction treesをpath trace inclusionでindexするとtrace-language graded monadを成す | WT-001; structural tree monad laws | strengthとvalue-type constructorsを追加 |
| C-098 | Derived | First-free-head transformer $\Phi_{\Delta,K}$ はmatching traceの最初の$\Delta$をclause language $K$で置換し、return/other-interface traceを保存するmonotone grade mapである | trace case analysis | composition/naturality lawsを計算 |
| C-099 | Derived | Tree shallow handlerは$\mathsf{Tree}_L X\to\mathsf{Tree}_{\Phi_{\Delta,K}(L)}X$を与え、direct operational semanticsの四ケースと一致する | WT-002 | Writer operational adequacyを証明 |
| C-100 | Counterexample | Optional bound $\Delta\mathbf w\Delta$ のtrace $\mathbf w\Delta$ はhandling後$\mathbf wK$となり、simple output $K\mathbf w\Delta$では一般にboundできない | noncommutativity; first optional token skipped | principal-word ruleの成立条件をcharacterize |
| C-101 | Derived | Writer grade embeddingは$J(1)=\{\epsilon\}$、$J(w)=\{\mathbf w^n\mid n\geq0\}$とすれば$w\cdot w=w$をlanguage multiplicationで保存する | Writer idempotence | general $B\to Q$ embedding条件を抽出 |
| C-102 | Derived conditional | Trace-language typing derivationはtree trace inclusionにsoundであり、handler caseは$\Phi_{\Delta,K}$で閉じる | WT-001--WT-002; T-Handle-Lang | mechanizationで全syntax casesを検査 |
| C-103 | Derived conditional | Internal reductionはunderlying Writer interaction tree denotationを保存する | substitution; tree monad laws; handler equations | formal proof termへ展開 |
| C-104 | Derived conditional | Recursion-free operational behavior treeはdenotational treeと一致し、ground Writer resultとfirst free requestを双方向に反映する | normalization; C-103; primitive node separation | reducibility measureを完全形式化 |
| C-105 | Derived conditional | Operational shallow handlerとstructural tree handlerはbehavior tree上で一致する | C-104; four handler head cases | nested handler casesを明示展開 |
| C-106 | Derived | Writer base-only treeは$\mathsf{List}(\mathsf{String})\times X$とreturn/bindを保存するcanonical isomorphismを持つ | run/quote calculation | grading compatibilityをdiagram化 |
| C-107 | Derived conditional | Structural tree relationはreturn/bindとexhaustive shallow handlerで保存される | pointwise continuation relation; related clauses | general relational lifting theoremへ抽象化 |
| C-108 | Milestone | Writer concrete modelで必要なsoundness/adequacy/conservativity/handler packageがpaper levelで閉じた | C-096--C-107 | Writer依存仮定と一般化可能部分を分離 |
| C-109 | Derived | $M=B*\mathcal D^*$ のdownset completionは一般base preorderとoptional free tokensを含むunital quantaleを成す | compatible monoid preorder | size条件とempty interfaceを確認 |
| C-110 | Derived | 任意のtyped algebraic base signatureについてbase/free nodeを持つ$\mathsf{GTree}$はdownset-language graded monadを成す | GB-001--GB-002 | categorical initialityを定式化 |
| C-111 | Derived | General structural shallow handlerはbase nodeだけを再帰的に通過し、最初のfree nodeで停止して$\Phi_{\Delta,K}$に従う | GB-003 | nested handler composition則を計算 |
| C-112 | Derived conditional | Typed/deterministic/head-normalizing base machineの下でbehavior-tree adequacyとhandler adequacyがWriter証明から一般化する | GB-004--GB-005 | base adequacyとの合成定理を精密化 |
| C-113 | Derived conditional | 任意のbase graded monad interpretation $T$ はtyped base-only treeからreturn/bind/primitiveを保存するfoldを受け取る | graded monad laws; primitive interpretations; coercion coherence | derivation independenceの範囲をcharacterize |
| C-114 | Rejected | 任意のbase graded monad $T$ についてbase-only free treeと$T$ carrierがcanonicalに同型である | nonfree/quotient/extra-element models | freeness/presentationを追加仮定として分離 |
| C-115 | Derived conditional | Primitive-preserving graded monad morphism $q:T\Rightarrow U$ はtyped foldsと可換する | GB-007 | strengthとhigher-order value casesを追加 |
| C-116 | Derived conditional | Structural tree relationはbindとexhaustive shallow handlersで保存され、relation-preserving foldsを介してtarget observationsへ輸送できる | GB-008 | fundamental lemmaのenvironment casesを展開 |
| C-117 | Main theorem candidate | Free extension theorem、base interpretation fold theorem、conditional adequacy theoremの三層が一般版の自然な主張である | C-109--C-116 | precise theorem statementsとassumption matrixを固定 |
| C-118 | Derived | Downset convolutionのclosure lemmaから$Q=\mathsf{Down}(B*\mathcal D^*)$のassociativity/unit/join-distributivityが従う | FE-002--FE-003 | formalizationでset extensionalityを展開 |
| C-119 | Derived | Trace-refined $\mathsf{GTree}$ はstrengthとcoherent inclusion weakeningを備えたstrong $Q$-graded monadである | FE-005--FE-010 | categorical recordへ整理 |
| C-120 | Derived | Exact handler-path lemmaによりexhaustive structural handlerは$\Phi_{\Delta,K}$でgradeされresult typeにnaturalである | FE-011--FE-015 | clause environment naturalityを追加確認 |
| C-121 | Derived | Gradeを忘れた$\mathsf{GTree}$はcombined polynomial signature上のfree monadである | FE-016; small W-types in Set | graded universal propertyの必要性を評価 |
| C-122 | Main theorem proved on paper | `Set`におけるFree extension theorem FE-017はquantale、strong graded monad、primitive、proof-irrelevant weakening、shallow handler、ungraded initialityを与える | C-118--C-121 | mechanizationまたはpeer proof audit |
| C-123 | Derived obstruction | pathwiseに$J(b)$でboundされたbase treeだけからは、任意のpreordered monoid上でroot後続枝の共通residual gradeを復元する原理が与えられない | absence of joins/factorization | concrete finite counterexampleまたは十分条件を追加 |
| C-124 | Derived | grade導出付き$\mathsf{BTree}_b$はtrace-soundでtyped return/bindを持つ | BI-001--BI-003 | mechanizationでderivation datatypeを実装 |
| C-125 | Derived | 任意のcoherent $B$-graded monadとgrade-correct primitivesはtyped base treeからreturn/bind/weakening/primitivesを保存するcanonical foldを受け取る | BI-004--BI-005 | source typing coherence theoremと接続 |
| C-126 | Derived | primitive-preserving graded monad morphismはtyped base foldsと可換する | BI-006 | logical relation版を証明 |
| C-127 | Main theorem proved on paper | Base interpretation layer BI-008はtyped fold、coherence、strength preservation、morphism liftingを与える | C-124--C-126 | conditional adequacy layerへ進む |
| C-128 | Derived conditional | OA-1--OA-5の下でclosed source computationのoperational behavior treeはcompositional $\mathsf{GTree}$ denotationと一致する | AD-001--AD-003 | full syntaxのlogical relationを展開 |
| C-129 | Derived conditional | direct shallow handlerのbehaviorはstructural first-free-head handlerと可換する | AD-004; four head cases | nested examplesを回帰試験化 |
| C-130 | Derived conditional | base observation adequacy BAを満たす任意の$T$へtyped foldを介してground adequacyをtransportできる | AD-006--AD-007; BI-008 | concrete non-Writer base modelで検証 |
| C-131 | Main theorem proved conditionally on paper | Adequacy layer AD-008はbehavior-tree equality、handler commutation、grade soundness、base observation transportを与える | C-128--C-130 | OA obligationsの完全証明とrecursion拡張 |
| C-132 | Derived | fixed Stage 2 calculusはreturn/internal/base/freeのunique combined decompositionを持つ | OD-001--OD-003; OS-001--OS-002 | mechanizationでmetalevel continuation extensionalityを扱う |
| C-133 | Derived | suspension response typingはprimitive inversionとresidual-context typingから従う | OD-004--OD-005; RC-001--RC-003 | accumulated machine trace configurationを型付け |
| C-134 | Derived | recursion-free Stage 2 calculusはshallow handlerを含むhereditary head normalizationを満たす | OD-006--OD-010 | reducibilityを形式化 |
| C-135 | Derived | clause fidelity OA-5はsemantic substitutionから従い、OA-4はnode-compatible base machineのinterface条件である | OD-011--OD-012 | non-Writer machine instanceを追加 |
| C-136 | Milestone | operational adequacy obligations OA-1--OA-5はfixed calculusとnode-compatible machineに対してpaper levelで閉じた | C-132--C-135 | base observation adequacy BAの一般条件を調べる |
| C-137 | Derived | target $T$からoperational base model $O$へのprimitive-preserving graded monad morphismは両者のtyped tree foldを一致させる | BA-001; BI-006 | relation-based variantを定式化 |
| C-138 | Derived | BAはfold comparisonにground observationをpostcomposeすることで導出できる | BA-002 | observation predicate版を形式化 |
| C-139 | Derived | graded State machineはBA criterionを満たし、initial/final stateとresultについてadequateである | BA-003 | free handlerを含むState program例を追加 |
| C-140 | Main theorem proved conditionally on algebraic interface | node-compatible $O$とprimitive-preserving $q:T\to O$があればhandled base-only programsのexact ground adequacyが従う | BA-004; OD-012; AD-004; BI-008 | logical relation criterionへ一般化 |
| C-141 | Derived | structural $\mathsf{TreeRel}$はmapとbindにcompatibleなfree-tree relatorである | LR-001--LR-003 | formalizationでW-type relationを定義 |
| C-142 | Derived | related exhaustive clausesの下でfirst-free-head shallow handlersはtree relationを保存する | LR-005--LR-006 | partial matcher extensionと比較 |
| C-143 | Derived | unit/bind/weakening/primitivesを保存するgraded computation relationはtyped base foldsを関連づける | LR-007 | strength付きopen-term版を完全展開 |
| C-144 | Derived | primitive-preserving graded monad morphismのequality graphからBI-006がLR-007の特殊例として回収される | LR-008 | general graph relatorとの対応を検討 |
| C-145 | Derived conditional | related source environmentsとclausesはhandled base-only programsのrelated ground observationsを導く | LR-009; observation compatibility | compiler transformation例で検証 |
| C-146 | Derived | nested shallow handlersのdenotationとoperational behaviorはstructural handler functionsのordered compositionである | HC-001--HC-002; AD-004 | nested syntax examplesを形式化 |
| C-147 | Derived | nested handler sequenceのsound gradeは対応する$\Phi$ transformersの同順序compositionである | HC-003--HC-004 | least-bound条件をcharacterize |
| C-148 | Counterexample | same-interface shallow handlerは一般にidempotentでなく、二重handlerは単一handlerへcollapseしない | HC-005--HC-006; two-tick tree | restricted idempotence domainを調べる |
| C-149 | Counterexample | distinct-interface shallow handlersとそのgrade transformersは一般にcommuteしない | HC-007; $\Delta\Gamma$ and clause-introduction examples | sufficient commutation conditionsを精密化 |
| C-150 | Derived conditional | head-separated domainではcross-interface introductionがなければ異なるhandlersはcommuteする | HC-008 | conditionをweakenできるか調べる |
| C-151 | Derived | mixed-word preorderはfree-interface token deletionとbase-factor loweringでcharacterizeできる | PW-001 | formal normal-form proofを実装 |
| C-152 | Derived | principal handler bound $b\Delta e\mapsto bke$は全later-matching residualについて$bak't\preceq bke$ iffでcharacterizeされる | PW-002 | decision procedureを検討 |
| C-153 | Derived | residual tail $e$がhandled interface $\Delta$を含まなければoriginal principal-word ruleはsoundである | PW-003 | source effect inferenceで利用 |
| C-154 | Counterexample | bound $\Delta w\Delta$のactual trace $w\Delta$はhandling後$wk$となり、一般に$kw\Delta$でboundされない | PW-005; noncommutative free model | original assumptionsとの対応を記述 |
| C-155 | Milestone | original $b\Delta e\mapsto bke$ ruleはcore axiomでなくPW-002のanchoring side condition付きderived ruleとして回収できる | C-151--C-154 | surface typing designへ反映 |
| C-156 | Derived | principal base downset $J(b)$に含まれるwordはbase-onlyである | BC-001--BC-002; PW-001 | formal normal-form proofへ統合 |
| C-157 | Derived | Stage 0 typing/execution/tree denotationはfree extensionへconservatively埋め込まれ、typed foldはfirst-order resultで元の$T$ denotationを回収しhigher-orderではlogical relationを満たす | BC-003--BC-006; BI-004; LR-007 | open-term categorical proofを完全図式化 |
| C-158 | Derived | shallow handlerと$\Phi$はbase-only trees/principal base languages上でidentityである | BC-007--BC-009 | source contextual equivalenceへ持ち上げる |
| C-159 | Counterexample | empty-response free operation nodeはcomplete traceを持たず任意のgradeに属するためunrestricted carrier reflectionは偽 | BC-010; $\mathsf{abort}:1\to0$ | maximal-partial-path gradingと比較 |
| C-160 | Derived conditional | 全operation response setsがinhabitedなら$\mathsf{GTree}_{J(b)}$の全要素はbase-onlyである | BC-011--BC-012 | assumptionをsource type grammarから導けるか確認 |
| C-161 | Milestone | free extensionのbase conservativityはcarrier isomorphismでなくsyntax embeddingとdenotation-preserving typed foldとして成立する | BC-013; C-156--C-160 | main theorem synthesisへ統合 |
| C-162 | Synthesis milestone | 研究の中心結果はopaque $T$のdirect extensionでなくfree interaction refinement + typed foldによるstructure-preserving extensionである | FE-017; BI-008; AD-008; BA-004; LR-009; BC-013 | literature novelty comparisonと論文outlineへ進む |
| C-163 | Future candidate | pathwise occurrence grades $\nu:\mathcal D\to\mathbb N_\infty$はsequencingを加算、branchingをmaxで解釈するquantitative effect systemを与える | Quantitative catch handlers direction | single-interface graded lawsを証明 |
| C-164 | Future conjecture | transparent searching catch-once handlerはexactly-once resumptionとclause count $k$の下で$n\mapsto(n-1)^++k$を満たす | C-163; first-matching transformer | trace abstractionから証明 |
| C-165 | Future conjecture | handler fuel $m$は$\Delta$-free clausesについて$n\mapsto(n-m)^+$を与え、$m=\omega$がdeep handlerへのbridgeになる | C-164; clause-scope choice | fuel semanticsとdeep equationsを比較 |
| C-166 | Adopted v2 definition | 新しいfree effectsはunordered may-rowで追跡し、base effect annotationとは分離する | Common free-handler calculus v2 | State/Exception instanceでprojection typingを検査 |
| C-167 | Adopted v2 definition | 標準deep handlerはnonmatching requestをpending handler付きcontinuationとしてforwardし、matching resumptionに自身を再設置する | Common free-handler calculus v2 | tree fold equationと照合 |
| C-168 | Derived on paper | Writer instanceはreturn、unique step、unique unhandled free requestの決定的分解を持つ | unique CBV context; deterministic `tell`; exhaustive nominal handlers | mechanizationまたはindependent proof audit |
| C-169 | Derived on paper | Writer instanceのdirect reductionはfree-row preservationとeffect-aware progressを満たす | C-168; value/resumption substitution; free-row-silent `tell` | derivation-level residual context proofを展開 |
| C-170 | Derived on paper | outward rowが$\Delta$を含まないexhaustive deep handlerから未処理$\Delta$ requestはescapeしない | C-169; deep reinstallation | denotational eliminationと対応付け |
| C-171 | Derived on paper | new syntaxを使わないWriter programは言語拡張に対してconservativeである | old reduction rules unchanged | denotational embeddingで再証明 |
| C-172 | Derived conditional | identity-return handlerはbase-only Writer programのvalueとlogを保存する | no free request; base steps lift under handler | nonidentity return clauseを明示的反例として保持 |
| C-173 | Counterexample | 同じfree row $\{\mathsf{Ask}\}$でもeffectful deep clauseのWriter出力は$\epsilon,a,aa$になりうるため、rowだけからprecise output base gradeは決まらない | zero/one/two request programs | principal-grade transformerの不可能性へ精密化 |
| C-174 | Derived on paper | Writer-normalized interaction tree $W\times(A+\sum P\times(R\to\mathsf{WTree}A))$ はrow-refined monadを成す | Writer monoid; well-founded free requests | formal monad recordまたはmechanization |
| C-175 | Derived on paper | standard deep handlerはmatching nodeをclauseで解釈し、nonmatching nodeのcontinuationへ再帰するtree foldとして定義できる | C-167; exhaustive clauses; WTree recursion | State transformer presentationと比較 |
| C-176 | Derived on paper | Writer direct reductionはconfiguration tree denotationを一stepごとに保存する | C-169; C-174--C-175; semantic substitution | 全congruence casesのindependent audit |
| C-177 | Derived conditional | closed evaluationがreturnまたはrequestへ到達するならWriter operational observationとWTreeのroot constructorは双方向に一致する | C-168; C-176; constructor disjointness | unrestricted multi-shot normalizationを証明 |
| C-178 | Impossibility theorem on paper | exact input Writer grade、unordered row、single clause gradeだけから全programのexact handled Writer gradeを計算する関数は存在しない | free Writer monoid; zero/one/two request counterexample | upper-bound transformerに必要な最小追加構造を比較 |

## 証明完了の基準

各 claim は最低限、次を持って初めて **Derived** とする。

- 全ての対象と射の型
- 使用した仮定の明示
- 等式なら可換図式または要素計算
- effect word の結合・subeffecting との整合性
- 境界例（空 interface、pure grade、空 tail）

文献に同様の定理があるだけでは、この台帳上の claim は Established/Derived にならない。
