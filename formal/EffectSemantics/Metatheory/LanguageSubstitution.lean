import EffectSemantics.Syntax.LanguageRenameSubst

namespace EffectSemantics

mutual
  def HasLanguageVal.rename_preserved
      (typing : source ⊢[sig] value :ᵥ ty)
      (preserves : LanguageRenPreserves source target rename) :
      target ⊢[sig] value.rename rename :ᵥ ty := by
    cases typing with
    | var lookup => exact .var (preserves lookup)
    | unit => exact .unit
    | bool => exact .bool
    | pair left right =>
        exact .pair (left.rename_preserved preserves)
          (right.rename_preserved preserves)
    | inl inner => exact .inl (inner.rename_preserved preserves)
    | inr inner => exact .inr (inner.rename_preserved preserves)
    | lam body => exact .lam (body.rename_preserved (preserves.lift _))
    | fixLam allowed body =>
        exact .fixLam allowed
          (body.rename_preserved ((preserves.lift _).lift _))
  termination_by (sizeOf value, sizeOf typing)

  def HasLanguageComp.rename_preserved
      (typing : source ⊢[sig] term : ty ! effect)
      (preserves : LanguageRenPreserves source target rename) :
      target ⊢[sig] term.rename rename : ty ! effect := by
    cases typing with
    | ret value => exact .ret (value.rename_preserved preserves)
    | letE bound body =>
        exact .letE (bound.rename_preserved preserves)
          (body.rename_preserved (preserves.lift _))
    | app function argument =>
        exact .app (function.rename_preserved preserves)
          (argument.rename_preserved preserves)
    | ite condition thenBranch elseBranch =>
        exact .ite (condition.rename_preserved preserves)
          (thenBranch.rename_preserved preserves)
          (elseBranch.rename_preserved preserves)
    | case scrutinee leftBranch rightBranch =>
        exact .case (scrutinee.rename_preserved preserves)
          (leftBranch.rename_preserved (preserves.lift _))
          (rightBranch.rename_preserved (preserves.lift _))
    | baseOp lookup parameter =>
        exact .baseOp lookup (parameter.rename_preserved preserves)
    | freeOp lookup parameter =>
        exact .freeOp lookup (parameter.rename_preserved preserves)
    | subeffect inner bound =>
        exact .subeffect (inner.rename_preserved preserves) bound
  termination_by (sizeOf term, sizeOf typing)
end

def LanguageSubstPreserves.lift
    (preserves : LanguageSubstPreserves sig source target subst)
    (head : LanguageTy) :
    LanguageSubstPreserves sig (head :: source) (head :: target)
      (liftLanguageSubst subst) := by
  intro index ty lookup
  cases index with
  | zero =>
      have equal : head = ty := Option.some.inj lookup
      subst ty
      exact .var rfl
  | succ index =>
      exact (preserves lookup).rename_preserved
        (LanguageRenPreserves.shift target head)

mutual
  def HasLanguageVal.subst_preserved
      (typing : source ⊢[sig] value :ᵥ ty)
      (preserves : LanguageSubstPreserves sig source target subst) :
      target ⊢[sig] value.subst subst :ᵥ ty := by
    cases typing with
    | var lookup => exact preserves lookup
    | unit => exact .unit
    | bool => exact .bool
    | pair left right =>
        exact .pair (left.subst_preserved preserves)
          (right.subst_preserved preserves)
    | inl inner => exact .inl (inner.subst_preserved preserves)
    | inr inner => exact .inr (inner.subst_preserved preserves)
    | lam body => exact .lam (body.subst_preserved (preserves.lift _))
    | fixLam allowed body =>
        exact .fixLam allowed
          (body.subst_preserved ((preserves.lift _).lift _))
  termination_by (sizeOf value, sizeOf typing)

  def HasLanguageComp.subst_preserved
      (typing : source ⊢[sig] term : ty ! effect)
      (preserves : LanguageSubstPreserves sig source target subst) :
      target ⊢[sig] term.subst subst : ty ! effect := by
    cases typing with
    | ret value => exact .ret (value.subst_preserved preserves)
    | letE bound body =>
        exact .letE (bound.subst_preserved preserves)
          (body.subst_preserved (preserves.lift _))
    | app function argument =>
        exact .app (function.subst_preserved preserves)
          (argument.subst_preserved preserves)
    | ite condition thenBranch elseBranch =>
        exact .ite (condition.subst_preserved preserves)
          (thenBranch.subst_preserved preserves)
          (elseBranch.subst_preserved preserves)
    | case scrutinee leftBranch rightBranch =>
        exact .case (scrutinee.subst_preserved preserves)
          (leftBranch.subst_preserved (preserves.lift _))
          (rightBranch.subst_preserved (preserves.lift _))
    | baseOp lookup parameter =>
        exact .baseOp lookup (parameter.subst_preserved preserves)
    | freeOp lookup parameter =>
        exact .freeOp lookup (parameter.subst_preserved preserves)
    | subeffect inner bound =>
        exact .subeffect (inner.subst_preserved preserves) bound
  termination_by (sizeOf term, sizeOf typing)
end

def languageSingleSubstPreserves
    (typing : ctx ⊢[sig] value :ᵥ valueTy) :
    LanguageSubstPreserves sig (valueTy :: ctx) ctx
      (fun | 0 => value | index + 1 => .var index) := by
  intro index found lookup
  cases index with
  | zero =>
      have equal : valueTy = found := Option.some.inj lookup
      subst found
      exact typing
  | succ index => exact .var lookup

def HasLanguageComp.subst0_preserved
    (bodyTyping : valueTy :: ctx ⊢[sig] body : bodyTy ! effect)
    (valueTyping : ctx ⊢[sig] value :ᵥ valueTy) :
    ctx ⊢[sig] body.subst0 value : bodyTy ! effect :=
  bodyTyping.subst_preserved (languageSingleSubstPreserves valueTyping)

def languageDoubleSubstPreserves
    (argumentTyping : ctx ⊢[sig] argument :ᵥ domain)
    (selfTyping : ctx ⊢[sig] self :ᵥ .arr domain latent codomain) :
    LanguageSubstPreserves sig
      (domain :: .arr domain latent codomain :: ctx) ctx
      (fun | 0 => argument | 1 => self | index + 2 => .var index) := by
  intro index found lookup
  cases index with
  | zero =>
      have equal : domain = found := Option.some.inj lookup
      subst found
      exact argumentTyping
  | succ index =>
      cases index with
      | zero =>
          have equal : LanguageTy.arr domain latent codomain = found :=
            Option.some.inj lookup
          subst found
          exact selfTyping
      | succ index => exact .var lookup

def HasLanguageComp.subst2_preserved
    (bodyTyping : domain :: .arr domain latent codomain :: ctx ⊢[sig]
      body : codomain ! latent)
    (argumentTyping : ctx ⊢[sig] argument :ᵥ domain)
    (selfTyping : ctx ⊢[sig] self :ᵥ .arr domain latent codomain) :
    ctx ⊢[sig] body.subst2 argument self : codomain ! latent :=
  bodyTyping.subst_preserved
    (languageDoubleSubstPreserves argumentTyping selfTyping)

end EffectSemantics
