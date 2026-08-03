# Work log

## 2026-08-04 — Notebook initialization

### Decisions

- 論文アウトラインを先に固定しない。
- 研究対象を「structure-preserving shallow extension」の候補として追跡する。
- operational/denotational models の間は、morphism だけでなく logical relation を第一級に扱う。
- category grading は当面の基礎仮定にせず、preordered monoid と handler/translation の構造を分離する。
- deep handlers、general recursion、形式化は後段に置く。

### Imported hypotheses from prior discussion

- extended effects は base effect と free interface の非可換な交互列として表せる可能性がある。
- shallow layer は coproduct・積・指数による polynomial extension として表せる可能性がある。
- この構成は graded monad morphism と graded logical relation の両方を持ち上げる可能性がある。
- adequacy は monad morphism だけでなく observation-reflecting relation を必要とする。

これらはまだ証明済みではないため Claims ledger では Conjecture/Candidate として登録した。

### Next mathematical task

Q-001 を埋め、最小 calculus の typing rules と operational observations を固定する。その後、Candidate A の unit と bind を完全に型付けして C-002 を検査する。

## 2026-08-04 — Minimal calculus v0

### Added

- fine-grain CBV の value/computation syntax
- explicit operation nodes
- standard shallow-handler reduction rules
- provisional sequential effect rules
- return、一回の operation、二回の operation、continuation 無視の test programs

### Important finding

標準的 shallow handler の return clause は値を受け取る。一方、既存の Candidate A の左 branch は tail computation \(\widehat T_eX\) である。したがって Candidate A を標準的 shallow-handler semantics と無条件に同一視できない。

これは表記上の小さな問題ではなく、head-normal decomposition と word-layer decomposition という二つの異なる意味論の可能性を示す。

### Next mathematical task

元の handler typing rule を復元するか、研究用の規則として head-normal / layer のどちらを採用するか決める。その判断まで C-002 の monad-law 証明は保留する。

## 2026-08-04 — Baseline calculus v1 adopted

### Fixed choices

- fine-grain CBV with value/computation separation
- noncommutative preordered monoid of effect upper bounds
- explicit operation nodes
- shallow continuation semantics
- leading-interface handler rule
- head-form observations for the first adequacy target

### Consequences

- 元の修論と完全一致する必要はなくなった。比較は後から行う。
- word-layer semantics は baseline の定義そのものではなく、handler-under-prefix を実現する拡張候補として再評価する。
- handler clause が continuation を無視する場合、tail effect を結果に課す必要はない。continuation の latent effect は function type に記録する。

### Next mathematical task

Baseline v1 の denotational interface を定義する。特に exposed operation を graded monad 内でどう表し、`R-Handle-Op` をどの普遍性または case analysis で解釈するかを比較する。
