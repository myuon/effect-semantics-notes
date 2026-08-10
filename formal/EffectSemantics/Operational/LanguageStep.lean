import EffectSemantics.Metatheory.LanguageSubstitution

namespace EffectSemantics

/-- Internal CBV reduction for the language-graded calculus. -/
inductive LanguageStep {mode : RecMode} :
    LanguageComp mode → LanguageComp mode → Type where
  | letReturn : LanguageStep (.letE (.ret value) body) (body.subst0 value)
  | beta : LanguageStep (.app (.lam domain latent body) argument)
      (body.subst0 argument)
  | fixBeta : LanguageStep
      (.app (.fixLam allowed domain latent body) argument)
      (body.subst2 argument (.fixLam allowed domain latent body))
  | ifTrue : LanguageStep (.ite (.bool true) thenBranch elseBranch) thenBranch
  | ifFalse : LanguageStep (.ite (.bool false) thenBranch elseBranch) elseBranch
  | caseInl : LanguageStep (.case (.inl value rightTy) leftBranch rightBranch)
      (leftBranch.subst0 value)
  | caseInr : LanguageStep (.case (.inr leftTy value) leftBranch rightBranch)
      (rightBranch.subst0 value)
  | underLet : LanguageStep bound bound' →
      LanguageStep (.letE bound body) (.letE bound' body)

/-- Internal one-step reduction for the language calculus. -/
infix:50 " ⟶ " => LanguageStep

def LanguageComp.internalStep {mode} :
    LanguageComp mode → Option (LanguageComp mode)
  | .ret _ => none
  | .letE (.ret value) body => some (body.subst0 value)
  | .letE bound body =>
      bound.internalStep.map (fun next => .letE next body)
  | .app (.lam _ _ body) argument => some (body.subst0 argument)
  | .app (.fixLam allowed domain latent body) argument =>
      some (body.subst2 argument (.fixLam allowed domain latent body))
  | .app _ _ => none
  | .ite (.bool true) thenBranch _ => some thenBranch
  | .ite (.bool false) _ elseBranch => some elseBranch
  | .ite _ _ _ => none
  | .case (.inl value _) leftBranch _ => some (leftBranch.subst0 value)
  | .case (.inr _ value) _ rightBranch => some (rightBranch.subst0 value)
  | .case _ _ _ => none
  | .baseOp _ _ => none
  | .freeOp _ _ _ => none

theorem LanguageStep.to_internalStep
    (step : term ⟶ next) : term.internalStep = some next := by
  induction step with
  | letReturn => rfl
  | beta => rfl
  | fixBeta => rfl
  | ifTrue => rfl
  | ifFalse => rfl
  | caseInl => rfl
  | caseInr => rfl
  | underLet inner ih =>
      cases inner <;> simp [LanguageComp.internalStep] at ih ⊢ <;> assumption

theorem LanguageStep.deterministic
    (first : term ⟶ left) (second : term ⟶ right) :
    left = right := by
  have firstEq := first.to_internalStep
  have secondEq := second.to_internalStep
  rw [firstEq] at secondEq
  exact Option.some.inj secondEq

end EffectSemantics
