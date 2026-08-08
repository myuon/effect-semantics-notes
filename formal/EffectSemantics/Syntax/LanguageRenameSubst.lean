import EffectSemantics.Syntax.LanguageCalculus

namespace EffectSemantics

def liftLanguageRen (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => rename index + 1

mutual
  def LanguageVal.rename (rename : Nat → Nat) : LanguageVal → LanguageVal
    | .var index => .var (rename index)
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.rename rename) (right.rename rename)
    | .inl value rightTy => .inl (value.rename rename) rightTy
    | .inr leftTy value => .inr leftTy (value.rename rename)
    | .lam domain latent body =>
        .lam domain latent (body.rename (liftLanguageRen rename))
    | .fixLam domain latent body =>
        .fixLam domain latent
          (body.rename (liftLanguageRen (liftLanguageRen rename)))

  def LanguageComp.rename (rename : Nat → Nat) : LanguageComp → LanguageComp
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

def liftLanguageSubst (subst : Nat → LanguageVal) : Nat → LanguageVal
  | 0 => .var 0
  | index + 1 => (subst index).rename (· + 1)

mutual
  def LanguageVal.subst (subst : Nat → LanguageVal) : LanguageVal → LanguageVal
    | .var index => subst index
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.subst subst) (right.subst subst)
    | .inl value rightTy => .inl (value.subst subst) rightTy
    | .inr leftTy value => .inr leftTy (value.subst subst)
    | .lam domain latent body =>
        .lam domain latent (body.subst (liftLanguageSubst subst))
    | .fixLam domain latent body =>
        .fixLam domain latent
          (body.subst (liftLanguageSubst (liftLanguageSubst subst)))

  def LanguageComp.subst (subst : Nat → LanguageVal) :
      LanguageComp → LanguageComp
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

def LanguageComp.subst0 (value : LanguageVal) (body : LanguageComp) :
    LanguageComp :=
  body.subst (fun | 0 => value | index + 1 => .var index)

def LanguageComp.subst2 (argument self : LanguageVal) (body : LanguageComp) :
    LanguageComp :=
  body.subst (fun | 0 => argument | 1 => self | index + 2 => .var index)

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

def LanguageSubstPreserves (sig : LanguageSignature)
    (source target : LanguageContext) (subst : Nat → LanguageVal) : Type :=
  ∀ ⦃index ty⦄, LanguageContext.lookup source index = some ty →
    HasLanguageVal sig target (subst index) ty

end EffectSemantics
