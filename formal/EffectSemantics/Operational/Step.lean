import EffectSemantics.Operational.Context

namespace EffectSemantics

/-- Pure/internal CBV reduction. Base and free operations are boundaries, not
internal reductions. -/
inductive Step : Comp → Comp → Prop where
  | letReturn : Step (.letE (.ret value) body) (body.subst0 value)
  | beta : Step (.app (.lam domain latent body) argument) (body.subst0 argument)
  | ifTrue : Step (.ite (.bool true) thenBranch elseBranch) thenBranch
  | ifFalse : Step (.ite (.bool false) thenBranch elseBranch) elseBranch
  | caseInl : Step (.case (.inl value rightTy) leftBranch rightBranch)
      (leftBranch.subst0 value)
  | caseInr : Step (.case (.inr leftTy value) leftBranch rightBranch)
      (rightBranch.subst0 value)
  | underLet : Step bound bound' → Step (.letE bound body) (.letE bound' body)

theorem Step.underContext {term term' : Comp} (step : Step term term') :
    ∀ ctx : EvalContext, Step (ctx.plug term) (ctx.plug term') := by
  intro ctx
  induction ctx generalizing term term' with
  | nil => exact step
  | cons frame rest ih =>
      cases frame with
      | letE body => exact ih (.underLet step)

end EffectSemantics
