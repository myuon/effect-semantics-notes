import EffectSemantics.Metatheory.LanguageNormalization

namespace EffectSemantics

set_option linter.defProp false in
mutual
  /-- Values in the old, base-only fragment of the language calculus. -/
  def LanguageVal.BaseOnly : LanguageVal mode → Prop
    | .var _ | .unit | .bool _ => True
    | .pair left right => left.BaseOnly ∧ right.BaseOnly
    | .inl value _ | .inr _ value => value.BaseOnly
    | .lam _ _ body | .fixLam _ _ _ body => body.BaseOnly

  /-- Computations that do not use a user-defined free operation. -/
  def LanguageComp.BaseOnly : LanguageComp mode → Prop
    | .ret value => value.BaseOnly
    | .letE bound body => bound.BaseOnly ∧ body.BaseOnly
    | .app function argument => function.BaseOnly ∧ argument.BaseOnly
    | .ite condition thenBranch elseBranch =>
        condition.BaseOnly ∧ thenBranch.BaseOnly ∧ elseBranch.BaseOnly
    | .case scrutinee leftBranch rightBranch =>
        scrutinee.BaseOnly ∧ leftBranch.BaseOnly ∧ rightBranch.BaseOnly
    | .baseOp _ parameter => parameter.BaseOnly
    | .freeOp _ _ _ => False
end

def LanguageBaseOnlySubstitution (substitution : Nat → LanguageVal mode) : Prop :=
  ∀ index, (substitution index).BaseOnly

mutual
  theorem LanguageVal.baseOnly_rename {value : LanguageVal mode}
      {rename : Nat → Nat} (baseOnly : value.BaseOnly) :
      (value.rename rename).BaseOnly := by
    cases value with
    | var | unit | bool => trivial
    | pair left right =>
        exact ⟨left.baseOnly_rename baseOnly.1, right.baseOnly_rename baseOnly.2⟩
    | inl value rightTy => exact value.baseOnly_rename baseOnly
    | inr leftTy value => exact value.baseOnly_rename baseOnly
    | lam domain latent body => exact body.baseOnly_rename baseOnly
    | fixLam allowed domain latent body => exact body.baseOnly_rename baseOnly

  theorem LanguageComp.baseOnly_rename {term : LanguageComp mode}
      {rename : Nat → Nat} (baseOnly : term.BaseOnly) :
      (term.rename rename).BaseOnly := by
    cases term with
    | ret value => exact value.baseOnly_rename baseOnly
    | letE bound body =>
        exact ⟨bound.baseOnly_rename baseOnly.1, body.baseOnly_rename baseOnly.2⟩
    | app function argument =>
        exact ⟨function.baseOnly_rename baseOnly.1, argument.baseOnly_rename baseOnly.2⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨condition.baseOnly_rename baseOnly.1,
          thenBranch.baseOnly_rename baseOnly.2.1,
          elseBranch.baseOnly_rename baseOnly.2.2⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨scrutinee.baseOnly_rename baseOnly.1,
          leftBranch.baseOnly_rename baseOnly.2.1,
          rightBranch.baseOnly_rename baseOnly.2.2⟩
    | baseOp operation parameter => exact parameter.baseOnly_rename baseOnly
    | freeOp => contradiction
end

theorem LanguageBaseOnlySubstitution.lift
    (baseOnly : LanguageBaseOnlySubstitution substitution) :
    LanguageBaseOnlySubstitution (liftLanguageSubst substitution) := by
  intro index
  cases index with
  | zero => trivial
  | succ index => exact LanguageVal.baseOnly_rename (baseOnly index)

mutual
  theorem LanguageVal.baseOnly_subst {value : LanguageVal mode}
      {substitution : Nat → LanguageVal mode} (valueOnly : value.BaseOnly)
      (substitutionOnly : LanguageBaseOnlySubstitution substitution) :
      (value.subst substitution).BaseOnly := by
    cases value with
    | var index => exact substitutionOnly index
    | unit | bool => trivial
    | pair left right =>
        exact ⟨left.baseOnly_subst valueOnly.1 substitutionOnly,
          right.baseOnly_subst valueOnly.2 substitutionOnly⟩
    | inl value rightTy => exact value.baseOnly_subst valueOnly substitutionOnly
    | inr leftTy value => exact value.baseOnly_subst valueOnly substitutionOnly
    | lam domain latent body =>
        exact body.baseOnly_subst valueOnly substitutionOnly.lift
    | fixLam allowed domain latent body =>
        exact body.baseOnly_subst valueOnly substitutionOnly.lift.lift

  theorem LanguageComp.baseOnly_subst {term : LanguageComp mode}
      {substitution : Nat → LanguageVal mode} (termOnly : term.BaseOnly)
      (substitutionOnly : LanguageBaseOnlySubstitution substitution) :
      (term.subst substitution).BaseOnly := by
    cases term with
    | ret value => exact value.baseOnly_subst termOnly substitutionOnly
    | letE bound body =>
        exact ⟨bound.baseOnly_subst termOnly.1 substitutionOnly,
          body.baseOnly_subst termOnly.2 substitutionOnly.lift⟩
    | app function argument =>
        exact ⟨function.baseOnly_subst termOnly.1 substitutionOnly,
          argument.baseOnly_subst termOnly.2 substitutionOnly⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨condition.baseOnly_subst termOnly.1 substitutionOnly,
          thenBranch.baseOnly_subst termOnly.2.1 substitutionOnly,
          elseBranch.baseOnly_subst termOnly.2.2 substitutionOnly⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨scrutinee.baseOnly_subst termOnly.1 substitutionOnly,
          leftBranch.baseOnly_subst termOnly.2.1 substitutionOnly.lift,
          rightBranch.baseOnly_subst termOnly.2.2 substitutionOnly.lift⟩
    | baseOp operation parameter =>
        exact parameter.baseOnly_subst termOnly substitutionOnly
    | freeOp => contradiction
end

theorem LanguageComp.baseOnly_subst0 {body : LanguageComp mode}
    {value : LanguageVal mode} (bodyOnly : body.BaseOnly)
    (valueOnly : value.BaseOnly) : (body.subst0 value).BaseOnly := by
  apply body.baseOnly_subst bodyOnly
  intro index
  cases index with
  | zero => exact valueOnly
  | succ index => trivial

theorem LanguageComp.baseOnly_subst2 {body : LanguageComp mode}
    {argument self : LanguageVal mode} (bodyOnly : body.BaseOnly)
    (argumentOnly : argument.BaseOnly) (selfOnly : self.BaseOnly) :
    (body.subst2 argument self).BaseOnly := by
  apply body.baseOnly_subst bodyOnly
  intro index
  cases index with
  | zero => exact argumentOnly
  | succ index =>
      cases index with
      | zero => exact selfOnly
      | succ index => trivial

/-- Internal evaluation of a base-only language term cannot introduce a free
operation, including through substitution and recursive unfolding. -/
theorem LanguageStep.preservesBaseOnly (step : term ⟶ next)
    (baseOnly : term.BaseOnly) : next.BaseOnly := by
  cases step with
  | letReturn => exact LanguageComp.baseOnly_subst0 baseOnly.2 baseOnly.1
  | beta => exact LanguageComp.baseOnly_subst0 baseOnly.1 baseOnly.2
  | fixBeta => exact LanguageComp.baseOnly_subst2 baseOnly.1 baseOnly.2 baseOnly.1
  | ifTrue => exact baseOnly.2.1
  | ifFalse => exact baseOnly.2.2
  | caseInl => exact LanguageComp.baseOnly_subst0 baseOnly.2.1 baseOnly.1
  | caseInr => exact LanguageComp.baseOnly_subst0 baseOnly.2.2 baseOnly.1
  | underLet inner => exact ⟨inner.preservesBaseOnly baseOnly.1, baseOnly.2⟩

theorem FinLanguageSteps.preservesBaseOnly (steps : FinLanguageSteps term result)
    (baseOnly : term.BaseOnly) : result.BaseOnly := by
  induction steps with
  | refl => exact baseOnly
  | head first rest ih => exact ih (first.preservesBaseOnly baseOnly)

/-- A boundary exposed by a base-only term is necessarily a base request. -/
theorem LanguageBoundary.kind_eq_base (boundary : LanguageBoundary term)
    (baseOnly : term.BaseOnly) : boundary.kind = .base := by
  induction boundary with
  | base => rfl
  | free => contradiction
  | underLet inner ih => exact ih baseOnly.1

/-- Current-language operational conservativity: internal evaluation of an
old-language term can never expose a user-defined free request. -/
theorem FinLanguageSteps.baseOnly_boundary_is_base
    (steps : FinLanguageSteps term result) (baseOnly : term.BaseOnly)
    (boundary : LanguageBoundary result) : boundary.kind = .base :=
  boundary.kind_eq_base (steps.preservesBaseOnly baseOnly)

end EffectSemantics
