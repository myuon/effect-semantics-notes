import EffectSemantics.Operational.LanguageStep

namespace EffectSemantics

open EffectLanguage

structure LanguageReturnView
    (typing : HasLanguageComp sig ctx (.ret value) ty effect) where
  valueTyping : HasLanguageVal sig ctx value ty
  pureBelow : principal 1 ≤ effect

def HasLanguageComp.returnView
    (typing : HasLanguageComp sig ctx (.ret value) ty effect) :
    LanguageReturnView typing := by
  cases typing with
  | ret valueTyping => exact ⟨valueTyping, EffectLanguage.le_refl _⟩
  | subeffect inner bound =>
      let view := inner.returnView
      exact ⟨view.valueTyping, EffectLanguage.le_trans view.pureBelow bound⟩

/-- Internal reduction preserves both the result type and the declared
language-valued may-effect bound. -/
def LanguageStep.preserve
    (step : LanguageStep term term')
    (typing : HasLanguageComp sig ctx term ty effect) :
    HasLanguageComp sig ctx term' ty effect := by
  cases typing with
  | ret valueTyping => cases step
  | baseOp lookup parameterTyping => cases step
  | freeOp lookup parameterTyping => cases step
  | subeffect inner bound => exact .subeffect (step.preserve inner) bound
  | letE boundTyping bodyTyping =>
      cases step with
      | letReturn =>
          let view := boundTyping.returnView
          have bodyResult := bodyTyping.subst0_preserved view.valueTyping
          exact HasLanguageComp.subeffect bodyResult
            (EffectLanguage.le_seq_of_pure_left view.pureBelow)
      | underLet boundStep => exact .letE (boundStep.preserve boundTyping) bodyTyping
  | app functionTyping argumentTyping =>
      cases step with
      | beta =>
          cases functionTyping with
          | lam bodyTyping => exact bodyTyping.subst0_preserved argumentTyping
      | fixBeta =>
          cases functionTyping with
          | fixLam recursive bodyTyping =>
              exact bodyTyping.subst2_preserved argumentTyping
                (HasLanguageVal.fixLam (allowed := _) bodyTyping)
  | ite conditionTyping thenTyping elseTyping =>
      cases step with
      | ifTrue =>
          exact .subeffect thenTyping (EffectLanguage.le_join_left _ _)
      | ifFalse =>
          exact .subeffect elseTyping (EffectLanguage.le_join_right _ _)
  | case scrutineeTyping leftTyping rightTyping =>
      cases step with
      | caseInl =>
          cases scrutineeTyping with
          | inl valueTyping =>
              exact .subeffect (leftTyping.subst0_preserved valueTyping)
                (EffectLanguage.le_join_left _ _)
      | caseInr =>
          cases scrutineeTyping with
          | inr valueTyping =>
              exact .subeffect (rightTyping.subst0_preserved valueTyping)
                (EffectLanguage.le_join_right _ _)

end EffectSemantics
