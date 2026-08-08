import EffectSemantics.Metatheory.LanguageSubstitution

namespace EffectSemantics

/-- Internal CBV reduction for the language-graded calculus. -/
inductive LanguageStep : LanguageComp → LanguageComp → Type where
  | letReturn : LanguageStep (.letE (.ret value) body) (body.subst0 value)
  | beta : LanguageStep (.app (.lam domain latent body) argument)
      (body.subst0 argument)
  | fixBeta : LanguageStep (.app (.fixLam domain latent body) argument)
      (body.subst2 argument (.fixLam domain latent body))
  | ifTrue : LanguageStep (.ite (.bool true) thenBranch elseBranch) thenBranch
  | ifFalse : LanguageStep (.ite (.bool false) thenBranch elseBranch) elseBranch
  | caseInl : LanguageStep (.case (.inl value rightTy) leftBranch rightBranch)
      (leftBranch.subst0 value)
  | caseInr : LanguageStep (.case (.inr leftTy value) leftBranch rightBranch)
      (rightBranch.subst0 value)
  | underLet : LanguageStep bound bound' →
      LanguageStep (.letE bound body) (.letE bound' body)

end EffectSemantics
