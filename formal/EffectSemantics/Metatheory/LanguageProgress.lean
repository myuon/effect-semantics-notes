import EffectSemantics.Metatheory.LanguagePreservation

namespace EffectSemantics

/-- An unhandled operation together with the surrounding CBV `let` stack. -/
inductive LanguageBoundary : LanguageComp → Type where
  | base : LanguageBoundary (.baseOp operation parameter)
  | free : LanguageBoundary (.freeOp interface operation parameter)
  | underLet : LanguageBoundary bound →
      LanguageBoundary (.letE bound body)

inductive LanguageProgress : LanguageComp → Type where
  | returned : LanguageProgress (.ret value)
  | internal : LanguageStep term term' → LanguageProgress term
  | boundary : LanguageBoundary term → LanguageProgress term

/-- Closed, well-typed language-graded computations return, reduce, or expose
one base/free boundary. -/
def HasLanguageComp.progressClosed
    (typing : HasLanguageComp sig [] term ty effect) :
    LanguageProgress term :=
  match typing with
  | .subeffect inner _ => inner.progressClosed
  | .ret _ => .returned
  | .baseOp _ _ => .boundary .base
  | .freeOp _ _ => .boundary .free
  | .letE boundTyping _ =>
      match boundTyping.progressClosed with
      | .returned => .internal .letReturn
      | .internal step => .internal (.underLet step)
      | .boundary request => .boundary (.underLet request)
  | .app functionTyping _ =>
      match functionTyping with
      | .var lookup => nomatch lookup
      | .lam _ => .internal .beta
      | .fixLam _ => .internal .fixBeta
  | .ite conditionTyping _ _ =>
      match conditionTyping with
      | .var lookup => nomatch lookup
      | .bool (value := true) => .internal .ifTrue
      | .bool (value := false) => .internal .ifFalse
  | .case scrutineeTyping _ _ =>
      match scrutineeTyping with
      | .var lookup => nomatch lookup
      | .inl _ => .internal .caseInl
      | .inr _ => .internal .caseInr

end EffectSemantics
