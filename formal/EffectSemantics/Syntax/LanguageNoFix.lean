import EffectSemantics.Operational.LanguageStep

namespace EffectSemantics

/-!
# The recursion-free source fragment

`LanguageVal` deliberately contains `fixLam` because Chapter IV extends the
same source language with recursion.  Chapters I--III quantify over the
structural fragment below instead of silently treating the full grammar as
strongly normalizing.
-/

mutual
  def LanguageVal.NoFix : LanguageVal → Prop
    | .var _ | .unit | .bool _ => True
    | .pair left right => left.NoFix ∧ right.NoFix
    | .inl value _ | .inr _ value => value.NoFix
    | .lam _ _ body => body.NoFix
    | .fixLam _ _ _ => False

  def LanguageComp.NoFix : LanguageComp → Prop
    | .ret value => value.NoFix
    | .letE bound body => bound.NoFix ∧ body.NoFix
    | .app function argument => function.NoFix ∧ argument.NoFix
    | .ite condition thenBranch elseBranch =>
        condition.NoFix ∧ thenBranch.NoFix ∧ elseBranch.NoFix
    | .case scrutinee leftBranch rightBranch =>
        scrutinee.NoFix ∧ leftBranch.NoFix ∧ rightBranch.NoFix
    | .baseOp _ parameter | .freeOp _ _ parameter => parameter.NoFix
end

def LanguageSubst.NoFix (subst : Nat → LanguageVal) : Prop :=
  ∀ index, (subst index).NoFix

mutual
  theorem LanguageVal.NoFix.rename
      (value : LanguageVal) (noFix : value.NoFix) (rename : Nat → Nat) :
      (value.rename rename).NoFix := by
    cases value with
    | var | unit | bool => trivial
    | pair left right =>
        exact ⟨LanguageVal.NoFix.rename left noFix.1 rename,
          LanguageVal.NoFix.rename right noFix.2 rename⟩
    | inl value rightTy => exact LanguageVal.NoFix.rename value noFix rename
    | inr leftTy value => exact LanguageVal.NoFix.rename value noFix rename
    | lam domain latent body =>
        exact LanguageComp.NoFix.rename body noFix (liftLanguageRen rename)
    | fixLam => contradiction
  termination_by (sizeOf value, sizeOf noFix)

  theorem LanguageComp.NoFix.rename
      (term : LanguageComp) (noFix : term.NoFix) (rename : Nat → Nat) :
      (term.rename rename).NoFix := by
    cases term with
    | ret value => exact LanguageVal.NoFix.rename value noFix rename
    | letE bound body =>
        exact ⟨LanguageComp.NoFix.rename bound noFix.1 rename,
          LanguageComp.NoFix.rename body noFix.2 (liftLanguageRen rename)⟩
    | app function argument =>
        exact ⟨LanguageVal.NoFix.rename function noFix.1 rename,
          LanguageVal.NoFix.rename argument noFix.2 rename⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨LanguageVal.NoFix.rename condition noFix.1 rename,
          LanguageComp.NoFix.rename thenBranch noFix.2.1 rename,
          LanguageComp.NoFix.rename elseBranch noFix.2.2 rename⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨LanguageVal.NoFix.rename scrutinee noFix.1 rename,
          LanguageComp.NoFix.rename leftBranch noFix.2.1 (liftLanguageRen rename),
          LanguageComp.NoFix.rename rightBranch noFix.2.2 (liftLanguageRen rename)⟩
    | baseOp operation parameter => exact LanguageVal.NoFix.rename parameter noFix rename
    | freeOp interface operation parameter =>
        exact LanguageVal.NoFix.rename parameter noFix rename
  termination_by (sizeOf term, sizeOf noFix)
end

theorem LanguageSubst.NoFix.lift
    {subst : Nat → LanguageVal} (noFix : LanguageSubst.NoFix subst) :
    LanguageSubst.NoFix (liftLanguageSubst subst) := by
  intro index
  cases index with
  | zero => trivial
  | succ index =>
      simpa [liftLanguageSubst] using
        LanguageVal.NoFix.rename (subst index) (noFix index) (fun index => index + 1)

mutual
  theorem LanguageVal.NoFix.subst
      (value : LanguageVal) {subst : Nat → LanguageVal}
      (noFix : value.NoFix) (substNoFix : LanguageSubst.NoFix subst) :
      (value.subst subst).NoFix := by
    cases value with
    | var index => exact substNoFix index
    | unit | bool => trivial
    | pair left right =>
        exact ⟨LanguageVal.NoFix.subst left noFix.1 substNoFix,
          LanguageVal.NoFix.subst right noFix.2 substNoFix⟩
    | inl value rightTy => exact LanguageVal.NoFix.subst value noFix substNoFix
    | inr leftTy value => exact LanguageVal.NoFix.subst value noFix substNoFix
    | lam domain latent body =>
        exact LanguageComp.NoFix.subst body noFix substNoFix.lift
    | fixLam => contradiction
  termination_by (sizeOf value, sizeOf noFix)

  theorem LanguageComp.NoFix.subst
      (term : LanguageComp) {subst : Nat → LanguageVal}
      (noFix : term.NoFix) (substNoFix : LanguageSubst.NoFix subst) :
      (term.subst subst).NoFix := by
    cases term with
    | ret value => exact LanguageVal.NoFix.subst value noFix substNoFix
    | letE bound body =>
        exact ⟨LanguageComp.NoFix.subst bound noFix.1 substNoFix,
          LanguageComp.NoFix.subst body noFix.2 substNoFix.lift⟩
    | app function argument =>
        exact ⟨LanguageVal.NoFix.subst function noFix.1 substNoFix,
          LanguageVal.NoFix.subst argument noFix.2 substNoFix⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨LanguageVal.NoFix.subst condition noFix.1 substNoFix,
          LanguageComp.NoFix.subst thenBranch noFix.2.1 substNoFix,
          LanguageComp.NoFix.subst elseBranch noFix.2.2 substNoFix⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨LanguageVal.NoFix.subst scrutinee noFix.1 substNoFix,
          LanguageComp.NoFix.subst leftBranch noFix.2.1 substNoFix.lift,
          LanguageComp.NoFix.subst rightBranch noFix.2.2 substNoFix.lift⟩
    | baseOp operation parameter =>
        exact LanguageVal.NoFix.subst parameter noFix substNoFix
    | freeOp interface operation parameter =>
        exact LanguageVal.NoFix.subst parameter noFix substNoFix
  termination_by (sizeOf term, sizeOf noFix)
end

theorem LanguageComp.NoFix.subst0
    {body : LanguageComp} {value : LanguageVal}
    (bodyNoFix : body.NoFix) (valueNoFix : value.NoFix) :
    (body.subst0 value).NoFix := by
  apply LanguageComp.NoFix.subst body bodyNoFix
  intro index
  cases index with
  | zero => exact valueNoFix
  | succ => trivial

/-- Internal reduction never introduces recursion into the recursion-free
fragment.  In particular, the `fixBeta` case is impossible. -/
theorem LanguageStep.preserve_noFix
    {term next : LanguageComp}
    (step : LanguageStep term next) (noFix : term.NoFix) : next.NoFix := by
  cases step with
  | letReturn => exact noFix.2.subst0 noFix.1
  | beta => exact LanguageComp.NoFix.subst0 noFix.1 noFix.2
  | fixBeta => exact False.elim noFix.1
  | ifTrue => exact noFix.2.1
  | ifFalse => exact noFix.2.2
  | caseInl => exact noFix.2.1.subst0 noFix.1
  | caseInr => exact noFix.2.2.subst0 noFix.1
  | underLet inner => exact ⟨inner.preserve_noFix noFix.1, noFix.2⟩

end EffectSemantics
