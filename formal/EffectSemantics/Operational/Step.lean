import EffectSemantics.Operational.Context

namespace EffectSemantics

/-- Pure/internal CBV reduction. Base and free operations are boundaries, not
internal reductions. -/
inductive Step : Comp → Comp → Type where
  | letReturn : Step (.letE (.ret value) body) (body.subst0 value)
  | beta : Step (.app (.lam domain latent body) argument) (body.subst0 argument)
  | ifTrue : Step (.ite (.bool true) thenBranch elseBranch) thenBranch
  | ifFalse : Step (.ite (.bool false) thenBranch elseBranch) elseBranch
  | caseInl : Step (.case (.inl value rightTy) leftBranch rightBranch)
      (leftBranch.subst0 value)
  | caseInr : Step (.case (.inr leftTy value) leftBranch rightBranch)
      (rightBranch.subst0 value)
  | underLet : Step bound bound' → Step (.letE bound body) (.letE bound' body)

def Comp.internalStep : Comp → Option Comp
  | .ret _ => none
  | .letE (.ret value) body => some (body.subst0 value)
  | .letE bound body => (bound.internalStep).map (fun bound' => .letE bound' body)
  | .app (.lam _ _ body) argument => some (body.subst0 argument)
  | .app _ _ => none
  | .ite (.bool true) thenBranch _ => some thenBranch
  | .ite (.bool false) _ elseBranch => some elseBranch
  | .ite _ _ _ => none
  | .case (.inl value _) leftBranch _ => some (leftBranch.subst0 value)
  | .case (.inr _ value) _ rightBranch => some (rightBranch.subst0 value)
  | .case _ _ _ => none
  | .baseOp _ _ => none
  | .freeOp _ _ _ => none

theorem Step.to_internalStep {term term' : Comp} (step : Step term term') :
    term.internalStep = some term' := by
  induction step with
  | letReturn => rfl
  | beta => rfl
  | ifTrue => rfl
  | ifFalse => rfl
  | caseInl => rfl
  | caseInr => rfl
  | underLet inner ih =>
      cases inner <;> simp [Comp.internalStep] at ih ⊢ <;> assumption

def Step.underContext {term term' : Comp} (step : Step term term') :
    (ctx : EvalContext) → Step (ctx.plug term) (ctx.plug term')
  | [] => step
  | .letE _ :: rest => Step.underContext (.underLet step) rest

end EffectSemantics
