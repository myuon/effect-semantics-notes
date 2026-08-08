import EffectSemantics.Operational.Boundary

namespace EffectSemantics

mutual
  def HasVal.rename_preserved {sig : Signature} {source target : Context}
      {value : Val} {ty : Ty} {rename : Nat → Nat}
      (typing : HasVal sig source value ty)
      (preserves : RenPreserves source target rename) :
      HasVal sig target (value.rename rename) ty := by
    cases typing with
    | var lookup => exact .var (preserves lookup)
    | unit => exact .unit
    | bool => exact .bool
    | pair leftTyping rightTyping =>
        exact .pair (leftTyping.rename_preserved preserves)
          (rightTyping.rename_preserved preserves)
    | inl valueTyping => exact .inl (valueTyping.rename_preserved preserves)
    | inr valueTyping => exact .inr (valueTyping.rename_preserved preserves)
    | lam bodyTyping =>
        exact .lam (bodyTyping.rename_preserved (preserves.lift _))
  termination_by (sizeOf value, sizeOf typing)

  def HasComp.rename_preserved {sig : Signature} {source target : Context}
      {term : Comp} {ty : Ty} {effect : Effect} {rename : Nat → Nat}
      (typing : HasComp sig source term ty effect)
      (preserves : RenPreserves source target rename) :
      HasComp sig target (term.rename rename) ty effect := by
    cases typing with
    | ret valueTyping => exact .ret (valueTyping.rename_preserved preserves)
    | letE boundTyping bodyTyping =>
        exact .letE (boundTyping.rename_preserved preserves)
          (bodyTyping.rename_preserved (preserves.lift _))
    | app functionTyping argumentTyping =>
        exact .app (functionTyping.rename_preserved preserves)
          (argumentTyping.rename_preserved preserves)
    | ite conditionTyping thenTyping elseTyping =>
        exact .ite (conditionTyping.rename_preserved preserves)
          (thenTyping.rename_preserved preserves) (elseTyping.rename_preserved preserves)
    | case scrutineeTyping leftTyping rightTyping =>
        exact .case (scrutineeTyping.rename_preserved preserves)
          (leftTyping.rename_preserved (preserves.lift _))
          (rightTyping.rename_preserved (preserves.lift _))
    | baseOp lookup parameterTyping =>
        exact .baseOp lookup (parameterTyping.rename_preserved preserves)
    | freeOp lookup parameterTyping =>
        exact .freeOp lookup (parameterTyping.rename_preserved preserves)
    | subeffect termTyping bound =>
        exact .subeffect (termTyping.rename_preserved preserves) bound
  termination_by (sizeOf term, sizeOf typing)
end

def SubstPreserves.lift {sig : Signature} {source target : Context}
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

mutual
  def HasVal.subst_preserved {sig : Signature} {source target : Context}
      {value : Val} {ty : Ty} {subst : Nat → Val}
      (typing : HasVal sig source value ty)
      (preserves : SubstPreserves sig source target subst) :
      HasVal sig target (value.subst subst) ty := by
    cases typing with
    | var lookup => exact preserves lookup
    | unit => exact .unit
    | bool => exact .bool
    | pair leftTyping rightTyping =>
        exact .pair (leftTyping.subst_preserved preserves)
          (rightTyping.subst_preserved preserves)
    | inl valueTyping => exact .inl (valueTyping.subst_preserved preserves)
    | inr valueTyping => exact .inr (valueTyping.subst_preserved preserves)
    | lam bodyTyping =>
        exact .lam (bodyTyping.subst_preserved (preserves.lift _))
  termination_by (sizeOf value, sizeOf typing)

  def HasComp.subst_preserved {sig : Signature} {source target : Context}
      {term : Comp} {ty : Ty} {effect : Effect} {subst : Nat → Val}
      (typing : HasComp sig source term ty effect)
      (preserves : SubstPreserves sig source target subst) :
      HasComp sig target (term.subst subst) ty effect := by
    cases typing with
    | ret valueTyping => exact .ret (valueTyping.subst_preserved preserves)
    | letE boundTyping bodyTyping =>
        exact .letE (boundTyping.subst_preserved preserves)
          (bodyTyping.subst_preserved (preserves.lift _))
    | app functionTyping argumentTyping =>
        exact .app (functionTyping.subst_preserved preserves)
          (argumentTyping.subst_preserved preserves)
    | ite conditionTyping thenTyping elseTyping =>
        exact .ite (conditionTyping.subst_preserved preserves)
          (thenTyping.subst_preserved preserves) (elseTyping.subst_preserved preserves)
    | case scrutineeTyping leftTyping rightTyping =>
        exact .case (scrutineeTyping.subst_preserved preserves)
          (leftTyping.subst_preserved (preserves.lift _))
          (rightTyping.subst_preserved (preserves.lift _))
    | baseOp lookup parameterTyping =>
        exact .baseOp lookup (parameterTyping.subst_preserved preserves)
    | freeOp lookup parameterTyping =>
        exact .freeOp lookup (parameterTyping.subst_preserved preserves)
    | subeffect termTyping bound =>
        exact .subeffect (termTyping.subst_preserved preserves) bound
  termination_by (sizeOf term, sizeOf typing)
end

def singleSubst (value : Val) : Nat → Val
  | 0 => value
  | n + 1 => .var n

def singleSubst_preserves {sig : Signature} {ctx : Context} {value : Val}
    {ty : Ty} (typing : HasVal sig ctx value ty) :
    SubstPreserves sig (ty :: ctx) ctx (singleSubst value) := by
  intro index found lookup
  cases index with
  | zero =>
      have eq : ty = found := Option.some.inj lookup
      subst found
      exact typing
  | succ n => exact .var lookup

def HasComp.subst0_preserved {sig : Signature} {ctx : Context}
    {body : Comp} {bodyTy valueTy : Ty} {effect : Effect} {value : Val}
    (bodyTyping : HasComp sig (valueTy :: ctx) body bodyTy effect)
    (valueTyping : HasVal sig ctx value valueTy) :
    HasComp sig ctx (body.subst0 value) bodyTy effect := by
  exact bodyTyping.subst_preserved (singleSubst_preserves valueTyping)

end EffectSemantics
