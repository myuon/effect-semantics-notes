import EffectSemantics.Syntax.LanguageCalculus
import Init.Omega

namespace EffectSemantics

def liftLanguageRen (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => rename index + 1

mutual
  def LanguageVal.rename {mode} (rename : Nat → Nat) :
      LanguageVal mode → LanguageVal mode
    | .var index => .var (rename index)
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.rename rename) (right.rename rename)
    | .inl value rightTy => .inl (value.rename rename) rightTy
    | .inr leftTy value => .inr leftTy (value.rename rename)
    | .lam domain latent body =>
        .lam domain latent (body.rename (liftLanguageRen rename))
    | .fixLam allowed domain latent body =>
        .fixLam allowed domain latent
          (body.rename (liftLanguageRen (liftLanguageRen rename)))

  def LanguageComp.rename {mode} (rename : Nat → Nat) :
      LanguageComp mode → LanguageComp mode
    | .ret value => .ret (value.rename rename)
    | .letE bound body =>
        .letE (bound.rename rename) (body.rename (liftLanguageRen rename))
    | .app function argument => .app (function.rename rename) (argument.rename rename)
    | .ite condition thenBranch elseBranch =>
        .ite (condition.rename rename) (thenBranch.rename rename)
          (elseBranch.rename rename)
    | .case scrutinee leftBranch rightBranch =>
        .case (scrutinee.rename rename)
          (leftBranch.rename (liftLanguageRen rename))
          (rightBranch.rename (liftLanguageRen rename))
    | .baseOp operation parameter => .baseOp operation (parameter.rename rename)
    | .freeOp interface operation parameter =>
        .freeOp interface operation (parameter.rename rename)
end

def liftLanguageSubst {mode} (subst : Nat → LanguageVal mode) :
    Nat → LanguageVal mode
  | 0 => .var 0
  | index + 1 => (subst index).rename (· + 1)

mutual
  def LanguageVal.subst {mode} (subst : Nat → LanguageVal mode) :
      LanguageVal mode → LanguageVal mode
    | .var index => subst index
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.subst subst) (right.subst subst)
    | .inl value rightTy => .inl (value.subst subst) rightTy
    | .inr leftTy value => .inr leftTy (value.subst subst)
    | .lam domain latent body =>
        .lam domain latent (body.subst (liftLanguageSubst subst))
    | .fixLam allowed domain latent body =>
        .fixLam allowed domain latent
          (body.subst (liftLanguageSubst (liftLanguageSubst subst)))

  def LanguageComp.subst {mode} (subst : Nat → LanguageVal mode) :
      LanguageComp mode → LanguageComp mode
    | .ret value => .ret (value.subst subst)
    | .letE bound body =>
        .letE (bound.subst subst) (body.subst (liftLanguageSubst subst))
    | .app function argument => .app (function.subst subst) (argument.subst subst)
    | .ite condition thenBranch elseBranch =>
        .ite (condition.subst subst) (thenBranch.subst subst)
          (elseBranch.subst subst)
    | .case scrutinee leftBranch rightBranch =>
        .case (scrutinee.subst subst)
          (leftBranch.subst (liftLanguageSubst subst))
          (rightBranch.subst (liftLanguageSubst subst))
    | .baseOp operation parameter => .baseOp operation (parameter.subst subst)
    | .freeOp interface operation parameter =>
        .freeOp interface operation (parameter.subst subst)
end

def LanguageComp.subst0 {mode} (value : LanguageVal mode)
    (body : LanguageComp mode) : LanguageComp mode :=
  body.subst (fun | 0 => value | index + 1 => .var index)

def LanguageComp.subst2 {mode} (argument self : LanguageVal mode)
    (body : LanguageComp mode) : LanguageComp mode :=
  body.subst (fun | 0 => argument | 1 => self | index + 2 => .var index)

mutual
  def LanguageVal.nodes {mode} : LanguageVal mode → Nat
    | .var _ | .unit | .bool _ => 1
    | .pair left right => left.nodes + right.nodes + 1
    | .inl value _ | .inr _ value => value.nodes + 1
    | .lam _ _ body | .fixLam _ _ _ body => body.nodes + 1

  def LanguageComp.nodes {mode} : LanguageComp mode → Nat
    | .ret value => value.nodes + 1
    | .letE bound body => bound.nodes + body.nodes + 1
    | .app function argument => function.nodes + argument.nodes + 1
    | .ite condition thenBranch elseBranch =>
        condition.nodes + thenBranch.nodes + elseBranch.nodes + 1
    | .case scrutinee leftBranch rightBranch =>
        scrutinee.nodes + leftBranch.nodes + rightBranch.nodes + 1
    | .baseOp _ parameter | .freeOp _ _ parameter => parameter.nodes + 1
end

mutual
  theorem LanguageVal.subst_rename_cancel
      {mode} (rename : Nat → Nat) (subst : Nat → LanguageVal mode)
      (cancel : ∀ index, subst (rename index) = .var index)
      (term : LanguageVal mode) :
      (term.rename rename).subst subst = term := by
    cases term with
    | var index => exact cancel index
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.subst_rename_cancel rename subst cancel left,
          LanguageVal.subst_rename_cancel rename subst cancel right]
    | inl inner rightTy =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.subst_rename_cancel rename subst cancel inner]
    | inr leftTy inner =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.subst_rename_cancel rename subst cancel inner]
    | lam domain latent body =>
        simp only [LanguageVal.rename, LanguageVal.subst]
        congr
        exact LanguageComp.subst_rename_cancel
          (liftLanguageRen rename) (liftLanguageSubst subst)
          (fun index => by
            cases index <;>
              simp [liftLanguageRen, liftLanguageSubst,
                LanguageVal.rename, cancel]) body
    | fixLam allowed domain latent body =>
        simp only [LanguageVal.rename, LanguageVal.subst]
        congr
        exact LanguageComp.subst_rename_cancel
          (liftLanguageRen (liftLanguageRen rename))
          (liftLanguageSubst (liftLanguageSubst subst))
          (fun index => by
            cases index with
            | zero => rfl
            | succ index =>
                cases index <;>
                  simp [liftLanguageRen, liftLanguageSubst,
                    LanguageVal.rename, cancel]) body

  theorem LanguageComp.subst_rename_cancel
      {mode} (rename : Nat → Nat) (subst : Nat → LanguageVal mode)
      (cancel : ∀ index, subst (rename index) = .var index)
      (term : LanguageComp mode) :
      (term.rename rename).subst subst = term := by
    cases term with
    | ret result =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.subst_rename_cancel rename subst cancel]
    | letE bound body =>
        simp only [LanguageComp.rename, LanguageComp.subst]
        congr
        · exact LanguageComp.subst_rename_cancel rename subst cancel bound
        · exact LanguageComp.subst_rename_cancel
            (liftLanguageRen rename) (liftLanguageSubst subst)
            (fun index => by
              cases index <;>
                simp [liftLanguageRen, liftLanguageSubst,
                  LanguageVal.rename, cancel]) body
    | app function argument =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.subst_rename_cancel rename subst cancel]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.subst_rename_cancel rename subst cancel,
          LanguageComp.subst_rename_cancel rename subst cancel thenBranch,
          LanguageComp.subst_rename_cancel rename subst cancel elseBranch]
    | case scrutinee leftBranch rightBranch =>
        simp only [LanguageComp.rename, LanguageComp.subst]
        congr
        · exact LanguageVal.subst_rename_cancel rename subst cancel scrutinee
        · exact LanguageComp.subst_rename_cancel
            (liftLanguageRen rename) (liftLanguageSubst subst)
            (fun index => by
              cases index <;>
                simp [liftLanguageRen, liftLanguageSubst,
                  LanguageVal.rename, cancel]) leftBranch
        · exact LanguageComp.subst_rename_cancel
            (liftLanguageRen rename) (liftLanguageSubst subst)
            (fun index => by
              cases index <;>
                simp [liftLanguageRen, liftLanguageSubst,
                  LanguageVal.rename, cancel]) rightBranch
    | baseOp operation parameter =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.subst_rename_cancel rename subst cancel]
    | freeOp interface operation parameter =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.subst_rename_cancel rename subst cancel]
end

def LanguageRenPreserves (source target : LanguageContext)
    (rename : Nat → Nat) : Prop :=
  ∀ ⦃index ty⦄, LanguageContext.lookup source index = some ty →
    LanguageContext.lookup target (rename index) = some ty

theorem LanguageRenPreserves.lift
    (preserves : LanguageRenPreserves source target rename) (head : LanguageTy) :
    LanguageRenPreserves (head :: source) (head :: target)
      (liftLanguageRen rename) := by
  intro index ty lookup
  cases index with
  | zero =>
      have equal : head = ty := Option.some.inj lookup
      subst ty
      rfl
  | succ index => exact preserves lookup

theorem LanguageRenPreserves.shift (ctx : LanguageContext) (head : LanguageTy) :
    LanguageRenPreserves ctx (head :: ctx) (· + 1) :=
  fun _ _ lookup => lookup

def LanguageSubstPreserves (sig : LanguageSignature) {mode}
    (source target : LanguageContext) (subst : Nat → LanguageVal mode) : Type :=
  ∀ ⦃index ty⦄, LanguageContext.lookup source index = some ty →
    HasLanguageVal sig target (subst index) ty

end EffectSemantics
