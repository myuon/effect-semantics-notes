import EffectSemantics.Metatheory.LanguagePreservation

namespace EffectSemantics

/-!
# Finite-to-recursive language embedding

The recursive calculus is a genuine conservative extension of the finite
calculus.  These definitions and theorems make that boundary explicit rather
than identifying the two source languages informally.
-/

mutual
  /-- Include a finite value in the recursive grammar. -/
  def LanguageVal.toRecursive : FinLanguageVal → RecLanguageVal
    | .var index => .var index
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair left.toRecursive right.toRecursive
    | .inl value rightTy => .inl value.toRecursive rightTy
    | .inr leftTy value => .inr leftTy value.toRecursive
    | .lam domain latent body => .lam domain latent body.toRecursive
    | .fixLam allowed _ _ _ => nomatch allowed

  /-- Include a finite computation in the recursive grammar. -/
  def LanguageComp.toRecursive : FinLanguageComp → RecLanguageComp
    | .ret value => .ret value.toRecursive
    | .letE bound body => .letE bound.toRecursive body.toRecursive
    | .app function argument => .app function.toRecursive argument.toRecursive
    | .ite condition thenBranch elseBranch =>
        .ite condition.toRecursive thenBranch.toRecursive elseBranch.toRecursive
    | .case scrutinee leftBranch rightBranch =>
        .case scrutinee.toRecursive leftBranch.toRecursive rightBranch.toRecursive
    | .baseOp operation parameter => .baseOp operation parameter.toRecursive
    | .freeOp interface operation parameter =>
        .freeOp interface operation parameter.toRecursive
end

mutual
  theorem LanguageVal.toRecursive_rename (value : FinLanguageVal)
      (rename : Nat → Nat) :
      (value.rename rename).toRecursive = value.toRecursive.rename rename := by
    cases value with
    | fixLam allowed _ _ _ => nomatch allowed
    | _ => simp [LanguageVal.toRecursive, LanguageVal.rename,
        LanguageComp.toRecursive_rename, LanguageVal.toRecursive_rename]

  theorem LanguageComp.toRecursive_rename (term : FinLanguageComp)
      (rename : Nat → Nat) :
      (term.rename rename).toRecursive = term.toRecursive.rename rename := by
    cases term <;> simp [LanguageComp.toRecursive, LanguageComp.rename,
      LanguageVal.toRecursive_rename, LanguageComp.toRecursive_rename]
end

def FinLanguageSubst.toRecursive (subst : Nat → FinLanguageVal) :
    Nat → RecLanguageVal := fun index => (subst index).toRecursive

theorem liftLanguageSubst_toRecursive (subst : Nat → FinLanguageVal) :
    FinLanguageSubst.toRecursive (liftLanguageSubst subst) =
      liftLanguageSubst (FinLanguageSubst.toRecursive subst) := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp [FinLanguageSubst.toRecursive, liftLanguageSubst,
        LanguageVal.toRecursive_rename]

mutual
  theorem LanguageVal.toRecursive_subst (value : FinLanguageVal)
      (subst : Nat → FinLanguageVal) :
      (value.subst subst).toRecursive =
        value.toRecursive.subst (FinLanguageSubst.toRecursive subst) := by
    cases value with
    | var index => rfl
    | fixLam allowed _ _ _ => nomatch allowed
    | _ => simp [LanguageVal.toRecursive, LanguageVal.subst,
        LanguageComp.toRecursive_subst, LanguageVal.toRecursive_subst,
        liftLanguageSubst_toRecursive]

  theorem LanguageComp.toRecursive_subst (term : FinLanguageComp)
      (subst : Nat → FinLanguageVal) :
      (term.subst subst).toRecursive =
        term.toRecursive.subst (FinLanguageSubst.toRecursive subst) := by
    cases term <;> simp [LanguageComp.toRecursive, LanguageComp.subst,
      LanguageVal.toRecursive_subst, LanguageComp.toRecursive_subst,
      liftLanguageSubst_toRecursive]
end

theorem LanguageComp.toRecursive_subst0 (body : FinLanguageComp)
    (value : FinLanguageVal) :
    (body.subst0 value).toRecursive = body.toRecursive.subst0 value.toRecursive := by
  rw [LanguageComp.subst0, LanguageComp.subst0,
    LanguageComp.toRecursive_subst]
  congr
  funext index
  cases index <;> rfl

/-- Every finite reduction is simulated by exactly one recursive reduction. -/
def LanguageStep.toRecursive
    (step : (term : FinLanguageComp) ⟶ next) :
    term.toRecursive ⟶ next.toRecursive := by
  cases step with
  | letReturn => simpa [LanguageComp.toRecursive,
      LanguageComp.toRecursive_subst0] using
      (LanguageStep.letReturn (mode := .recursive))
  | beta => simpa [LanguageComp.toRecursive,
      LanguageVal.toRecursive, LanguageComp.toRecursive_subst0] using
      (LanguageStep.beta (mode := .recursive))
  | fixBeta => contradiction
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | caseInl => simpa [LanguageComp.toRecursive,
      LanguageVal.toRecursive, LanguageComp.toRecursive_subst0] using
      (LanguageStep.caseInl (mode := .recursive))
  | caseInr => simpa [LanguageComp.toRecursive,
      LanguageVal.toRecursive, LanguageComp.toRecursive_subst0] using
      (LanguageStep.caseInr (mode := .recursive))
  | underLet inner => exact .underLet inner.toRecursive

end EffectSemantics
