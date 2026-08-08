import EffectSemantics.Operational.Boundary

namespace EffectSemantics

theorem HasVal.rename_preserved {sig : Signature} {source target : Context}
    {value : Val} {ty : Ty} {rename : Nat → Nat}
    (typing : HasVal sig source value ty)
    (preserves : RenPreserves source target rename) :
    HasVal sig target (value.rename rename) ty := by
  induction typing using HasVal.rec generalizing target rename preserves with
  | var lookup => exact .var (preserves lookup)
  | unit => exact .unit
  | bool => exact .bool
  | pair _ _ leftIH rightIH => exact .pair (leftIH preserves) (rightIH preserves)
  | inl _ valueIH => exact .inl (valueIH preserves)
  | inr _ valueIH => exact .inr (valueIH preserves)
  | lam _ bodyIH => exact .lam (bodyIH (preserves.lift _))
  | ret _ valueIH => exact .ret (valueIH preserves)
  | letE _ _ boundIH bodyIH =>
      exact .letE (boundIH preserves) (bodyIH (preserves.lift _))
  | app _ _ functionIH argumentIH => exact .app (functionIH preserves) (argumentIH preserves)
  | ite _ _ _ conditionIH thenIH elseIH =>
      exact .ite (conditionIH preserves) (thenIH preserves) (elseIH preserves)
  | case _ _ _ scrutineeIH leftIH rightIH =>
      exact .case (scrutineeIH preserves) (leftIH (preserves.lift _))
        (rightIH (preserves.lift _))
  | baseOp lookup _ parameterIH => exact .baseOp lookup (parameterIH preserves)
  | freeOp lookup _ parameterIH => exact .freeOp lookup (parameterIH preserves)
  | subeffect _ bound termIH => exact .subeffect (termIH preserves) bound

theorem HasComp.rename_preserved {sig : Signature} {source target : Context}
    {term : Comp} {ty : Ty} {effect : Effect} {rename : Nat → Nat}
    (typing : HasComp sig source term ty effect)
    (preserves : RenPreserves source target rename) :
    HasComp sig target (term.rename rename) ty effect := by
  induction typing using HasComp.rec generalizing target rename preserves with
  | var lookup => exact .var (preserves lookup)
  | unit => exact .unit
  | bool => exact .bool
  | pair _ _ leftIH rightIH => exact .pair (leftIH preserves) (rightIH preserves)
  | inl _ valueIH => exact .inl (valueIH preserves)
  | inr _ valueIH => exact .inr (valueIH preserves)
  | lam _ bodyIH => exact .lam (bodyIH (preserves.lift _))
  | ret _ valueIH => exact .ret (valueIH preserves)
  | letE _ _ boundIH bodyIH =>
      exact .letE (boundIH preserves) (bodyIH (preserves.lift _))
  | app _ _ functionIH argumentIH => exact .app (functionIH preserves) (argumentIH preserves)
  | ite _ _ _ conditionIH thenIH elseIH =>
      exact .ite (conditionIH preserves) (thenIH preserves) (elseIH preserves)
  | case _ _ _ scrutineeIH leftIH rightIH =>
      exact .case (scrutineeIH preserves) (leftIH (preserves.lift _))
        (rightIH (preserves.lift _))
  | baseOp lookup _ parameterIH => exact .baseOp lookup (parameterIH preserves)
  | freeOp lookup _ parameterIH => exact .freeOp lookup (parameterIH preserves)
  | subeffect _ bound termIH => exact .subeffect (termIH preserves) bound

theorem SubstPreserves.lift {sig : Signature} {source target : Context}
    {subst : Nat → Val} (h : SubstPreserves sig source target subst) (head : Ty) :
    SubstPreserves sig (head :: source) (head :: target) (liftSubst subst) := by
  intro index ty lookup
  cases index with
  | zero =>
      have eq : head = ty := Option.some.inj lookup
      subst ty
      exact .var rfl
  | succ n =>
      simp only [Context.lookup_succ] at lookup
      exact (h lookup).rename_preserved (RenPreserves.shift target head)

theorem HasVal.subst_preserved {sig : Signature} {source target : Context}
    {value : Val} {ty : Ty} {subst : Nat → Val}
    (typing : HasVal sig source value ty)
    (preserves : SubstPreserves sig source target subst) :
    HasVal sig target (value.subst subst) ty := by
  induction typing using HasVal.rec generalizing target subst preserves with
  | var lookup => exact preserves lookup
  | unit => exact .unit
  | bool => exact .bool
  | pair _ _ leftIH rightIH => exact .pair (leftIH preserves) (rightIH preserves)
  | inl _ valueIH => exact .inl (valueIH preserves)
  | inr _ valueIH => exact .inr (valueIH preserves)
  | lam _ bodyIH => exact .lam (bodyIH (preserves.lift _))
  | ret _ valueIH => exact .ret (valueIH preserves)
  | letE _ _ boundIH bodyIH =>
      exact .letE (boundIH preserves) (bodyIH (preserves.lift _))
  | app _ _ functionIH argumentIH => exact .app (functionIH preserves) (argumentIH preserves)
  | ite _ _ _ conditionIH thenIH elseIH =>
      exact .ite (conditionIH preserves) (thenIH preserves) (elseIH preserves)
  | case _ _ _ scrutineeIH leftIH rightIH =>
      exact .case (scrutineeIH preserves) (leftIH (preserves.lift _))
        (rightIH (preserves.lift _))
  | baseOp lookup _ parameterIH => exact .baseOp lookup (parameterIH preserves)
  | freeOp lookup _ parameterIH => exact .freeOp lookup (parameterIH preserves)
  | subeffect _ bound termIH => exact .subeffect (termIH preserves) bound

theorem HasComp.subst_preserved {sig : Signature} {source target : Context}
    {term : Comp} {ty : Ty} {effect : Effect} {subst : Nat → Val}
    (typing : HasComp sig source term ty effect)
    (preserves : SubstPreserves sig source target subst) :
    HasComp sig target (term.subst subst) ty effect := by
  induction typing using HasComp.rec generalizing target subst preserves with
  | var lookup => exact preserves lookup
  | unit => exact .unit
  | bool => exact .bool
  | pair _ _ leftIH rightIH => exact .pair (leftIH preserves) (rightIH preserves)
  | inl _ valueIH => exact .inl (valueIH preserves)
  | inr _ valueIH => exact .inr (valueIH preserves)
  | lam _ bodyIH => exact .lam (bodyIH (preserves.lift _))
  | ret _ valueIH => exact .ret (valueIH preserves)
  | letE _ _ boundIH bodyIH =>
      exact .letE (boundIH preserves) (bodyIH (preserves.lift _))
  | app _ _ functionIH argumentIH => exact .app (functionIH preserves) (argumentIH preserves)
  | ite _ _ _ conditionIH thenIH elseIH =>
      exact .ite (conditionIH preserves) (thenIH preserves) (elseIH preserves)
  | case _ _ _ scrutineeIH leftIH rightIH =>
      exact .case (scrutineeIH preserves) (leftIH (preserves.lift _))
        (rightIH (preserves.lift _))
  | baseOp lookup _ parameterIH => exact .baseOp lookup (parameterIH preserves)
  | freeOp lookup _ parameterIH => exact .freeOp lookup (parameterIH preserves)
  | subeffect _ bound termIH => exact .subeffect (termIH preserves) bound

def singleSubst (value : Val) : Nat → Val
  | 0 => value
  | n + 1 => .var n

theorem singleSubst_preserves {sig : Signature} {ctx : Context} {value : Val}
    {ty : Ty} (typing : HasVal sig ctx value ty) :
    SubstPreserves sig (ty :: ctx) ctx (singleSubst value) := by
  intro index found lookup
  cases index with
  | zero =>
      have eq : ty = found := Option.some.inj lookup
      subst found
      exact typing
  | succ n => exact .var lookup

theorem HasComp.subst0_preserved {sig : Signature} {ctx : Context}
    {body : Comp} {bodyTy valueTy : Ty} {effect : Effect} {value : Val}
    (bodyTyping : HasComp sig (valueTy :: ctx) body bodyTy effect)
    (valueTyping : HasVal sig ctx value valueTy) :
    HasComp sig ctx (body.subst0 value) bodyTy effect := by
  exact bodyTyping.subst_preserved (singleSubst_preserves valueTyping)

end EffectSemantics
