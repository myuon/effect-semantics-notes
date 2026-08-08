import EffectSemantics.Syntax.Signature

namespace EffectSemantics

mutual
  /-- Fine-grain CBV values with de Bruijn variables. -/
  inductive Val where
    | var (index : Nat)
    | unit
    | bool (value : Bool)
    | pair (left right : Val)
    | inl (value : Val) (rightTy : Ty)
    | inr (leftTy : Ty) (value : Val)
    | lam (domain : Ty) (latent : Effect) (body : Comp)
    | fixLam (domain : Ty) (latent : Effect) (body : Comp)
    deriving DecidableEq, Repr

  /-- Fine-grain computations.  Operations are ordinary computations and do
  not syntactically receive a continuation. -/
  inductive Comp where
    | ret (value : Val)
    | letE (bound : Comp) (body : Comp)
    | app (function argument : Val)
    | ite (condition : Val) (thenBranch elseBranch : Comp)
    | case (scrutinee : Val) (leftBranch rightBranch : Comp)
    | baseOp (operation : Nat) (parameter : Val)
    | freeOp (interface operation : Nat) (parameter : Val)
    deriving DecidableEq, Repr
end

abbrev Context := List Ty

def Context.lookup : Context → Nat → Option Ty
  | [], _ => none
  | ty :: _, 0 => some ty
  | _ :: rest, n + 1 => Context.lookup rest n

@[simp] theorem Context.lookup_zero (ty : Ty) (ctx : Context) :
    Context.lookup (ty :: ctx) 0 = some ty := rfl

@[simp] theorem Context.lookup_succ (ty : Ty) (ctx : Context) (n : Nat) :
    Context.lookup (ty :: ctx) (n + 1) = Context.lookup ctx n := rfl

end EffectSemantics
