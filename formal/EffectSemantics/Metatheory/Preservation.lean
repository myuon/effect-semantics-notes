import EffectSemantics.Metatheory.Inversion

namespace EffectSemantics

/-- Internal reduction preserves result type and the declared ordered effect
upper bound. -/
def Step.preserve {sig : Signature} {ctx : Context} {term term' : Comp}
    {ty : Ty} {effect : Effect} (step : Step term term')
    (typing : HasComp sig ctx term ty effect) : HasComp sig ctx term' ty effect := by
  cases typing with
  | ret valueTyping => cases step
  | baseOp lookup parameterTyping => cases step
  | freeOp lookup parameterTyping => cases step
  | subeffect inner bound => exact .subeffect (step.preserve inner) bound
  | letE boundTyping bodyTyping =>
      cases step with
      | letReturn =>
          let view := boundTyping.returnView
          exact (bodyTyping.subst0_preserved view.valueTyping).subeffect
            (Effect.le_left_padding _ _)
      | underLet boundStep => exact .letE (boundStep.preserve boundTyping) bodyTyping
  | app functionTyping argumentTyping =>
      cases step with
      | beta =>
          cases functionTyping with
          | lam bodyTyping => exact bodyTyping.subst0_preserved argumentTyping
  | ite conditionTyping thenTyping elseTyping =>
      cases step with
      | ifTrue => exact thenTyping
      | ifFalse => exact elseTyping
  | case scrutineeTyping leftTyping rightTyping =>
      cases step with
      | caseInl =>
          cases scrutineeTyping with
          | inl valueTyping => exact leftTyping.subst0_preserved valueTyping
      | caseInr =>
          cases scrutineeTyping with
          | inr valueTyping => exact rightTyping.subst0_preserved valueTyping

end EffectSemantics
