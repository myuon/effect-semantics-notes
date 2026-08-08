import EffectSemantics.Syntax.Typing

namespace EffectSemantics

def liftRen (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rename n + 1

mutual
  def Val.rename (rename : Nat → Nat) : Val → Val
    | .var index => .var (rename index)
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.rename rename) (right.rename rename)
    | .inl value rightTy => .inl (value.rename rename) rightTy
    | .inr leftTy value => .inr leftTy (value.rename rename)
    | .lam domain latent body => .lam domain latent (body.rename (liftRen rename))

  def Comp.rename (rename : Nat → Nat) : Comp → Comp
    | .ret value => .ret (value.rename rename)
    | .letE bound body => .letE (bound.rename rename) (body.rename (liftRen rename))
    | .app function argument => .app (function.rename rename) (argument.rename rename)
    | .ite condition thenBranch elseBranch =>
        .ite (condition.rename rename) (thenBranch.rename rename) (elseBranch.rename rename)
    | .case scrutinee leftBranch rightBranch =>
        .case (scrutinee.rename rename) (leftBranch.rename (liftRen rename))
          (rightBranch.rename (liftRen rename))
    | .baseOp operation parameter => .baseOp operation (parameter.rename rename)
    | .freeOp interface operation parameter =>
        .freeOp interface operation (parameter.rename rename)
end

def liftSubst (subst : Nat → Val) : Nat → Val
  | 0 => .var 0
  | n + 1 => (subst n).rename (· + 1)

mutual
  def Val.subst (subst : Nat → Val) : Val → Val
    | .var index => subst index
    | .unit => .unit
    | .bool value => .bool value
    | .pair left right => .pair (left.subst subst) (right.subst subst)
    | .inl value rightTy => .inl (value.subst subst) rightTy
    | .inr leftTy value => .inr leftTy (value.subst subst)
    | .lam domain latent body => .lam domain latent (body.subst (liftSubst subst))

  def Comp.subst (subst : Nat → Val) : Comp → Comp
    | .ret value => .ret (value.subst subst)
    | .letE bound body => .letE (bound.subst subst) (body.subst (liftSubst subst))
    | .app function argument => .app (function.subst subst) (argument.subst subst)
    | .ite condition thenBranch elseBranch =>
        .ite (condition.subst subst) (thenBranch.subst subst) (elseBranch.subst subst)
    | .case scrutinee leftBranch rightBranch =>
        .case (scrutinee.subst subst) (leftBranch.subst (liftSubst subst))
          (rightBranch.subst (liftSubst subst))
    | .baseOp operation parameter => .baseOp operation (parameter.subst subst)
    | .freeOp interface operation parameter =>
        .freeOp interface operation (parameter.subst subst)
end

/-- Substitute a closed value for the newest variable. -/
def Comp.subst0 (value : Val) (body : Comp) : Comp :=
  body.subst (fun | 0 => value | n + 1 => .var n)

def RenPreserves (source target : Context) (rename : Nat → Nat) : Prop :=
  ∀ ⦃index ty⦄, Context.lookup source index = some ty →
    Context.lookup target (rename index) = some ty

theorem RenPreserves.lift {source target : Context} {rename : Nat → Nat}
    (h : RenPreserves source target rename) (head : Ty) :
    RenPreserves (head :: source) (head :: target) (liftRen rename) := by
  intro index ty lookup
  cases index with
  | zero =>
      have eq : head = ty := Option.some.inj lookup
      subst ty
      rfl
  | succ n =>
      simp only [Context.lookup_succ] at lookup ⊢
      exact h lookup

theorem RenPreserves.shift (ctx : Context) (head : Ty) :
    RenPreserves ctx (head :: ctx) (· + 1) := by
  intro index ty lookup
  simpa using lookup

def SubstPreserves (sig : Signature) (source target : Context)
    (subst : Nat → Val) : Prop :=
  ∀ ⦃index ty⦄, Context.lookup source index = some ty →
    HasVal sig target (subst index) ty

end EffectSemantics
