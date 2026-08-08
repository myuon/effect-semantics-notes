import EffectSemantics.Denotational.EffectLanguage

namespace EffectSemantics

open EffectLanguage

/-- Value types for the conservative language-graded source calculus. -/
inductive LanguageTy where
  | unit
  | bool
  | prod (left right : LanguageTy)
  | sum (left right : LanguageTy)
  | arr (domain : LanguageTy) (latent : EffectLanguage) (codomain : LanguageTy)

structure LanguageOpDecl where
  parameter : LanguageTy
  response : LanguageTy

structure LanguageSignature where
  base : Nat → Option LanguageOpDecl
  free : Nat → Nat → Option LanguageOpDecl

mutual
  inductive LanguageVal where
    | var (index : Nat)
    | unit
    | bool (value : Bool)
    | pair (left right : LanguageVal)
    | inl (value : LanguageVal) (rightTy : LanguageTy)
    | inr (leftTy : LanguageTy) (value : LanguageVal)
    | lam (domain : LanguageTy) (latent : EffectLanguage) (body : LanguageComp)
    | fixLam (domain : LanguageTy) (latent : EffectLanguage) (body : LanguageComp)

  inductive LanguageComp where
    | ret (value : LanguageVal)
    | letE (bound : LanguageComp) (body : LanguageComp)
    | app (function argument : LanguageVal)
    | ite (condition : LanguageVal) (thenBranch elseBranch : LanguageComp)
    | case (scrutinee : LanguageVal) (leftBranch rightBranch : LanguageComp)
    | baseOp (operation : Nat) (parameter : LanguageVal)
    | freeOp (interface operation : Nat) (parameter : LanguageVal)
end

abbrev LanguageContext := List LanguageTy

def LanguageContext.lookup : LanguageContext → Nat → Option LanguageTy
  | [], _ => none
  | ty :: _, 0 => some ty
  | _ :: rest, index + 1 => LanguageContext.lookup rest index

mutual
  inductive HasLanguageVal (sig : LanguageSignature) :
      LanguageContext → LanguageVal → LanguageTy → Type where
    | var : LanguageContext.lookup ctx index = some ty →
        HasLanguageVal sig ctx (.var index) ty
    | unit : HasLanguageVal sig ctx .unit .unit
    | bool : HasLanguageVal sig ctx (.bool value) .bool
    | pair : HasLanguageVal sig ctx left leftTy →
        HasLanguageVal sig ctx right rightTy →
        HasLanguageVal sig ctx (.pair left right) (.prod leftTy rightTy)
    | inl : HasLanguageVal sig ctx value leftTy →
        HasLanguageVal sig ctx (.inl value rightTy) (.sum leftTy rightTy)
    | inr : HasLanguageVal sig ctx value rightTy →
        HasLanguageVal sig ctx (.inr leftTy value) (.sum leftTy rightTy)
    | lam : HasLanguageComp sig (domain :: ctx) body codomain latent →
        HasLanguageVal sig ctx (.lam domain latent body) (.arr domain latent codomain)
    | fixLam :
        HasLanguageComp sig (domain :: .arr domain latent codomain :: ctx)
          body codomain latent →
        HasLanguageVal sig ctx (.fixLam domain latent body)
          (.arr domain latent codomain)

  inductive HasLanguageComp (sig : LanguageSignature) :
      LanguageContext → LanguageComp → LanguageTy → EffectLanguage → Type where
    | ret : HasLanguageVal sig ctx value ty →
        HasLanguageComp sig ctx (.ret value) ty (principal 1)
    | letE : HasLanguageComp sig ctx bound boundTy boundEffect →
        HasLanguageComp sig (boundTy :: ctx) body resultTy bodyEffect →
        HasLanguageComp sig ctx (.letE bound body) resultTy
          (EffectLanguage.seq boundEffect bodyEffect)
    | app : HasLanguageVal sig ctx function (.arr domain latent codomain) →
        HasLanguageVal sig ctx argument domain →
        HasLanguageComp sig ctx (.app function argument) codomain latent
    | ite : HasLanguageVal sig ctx condition .bool →
        HasLanguageComp sig ctx thenBranch ty thenEffect →
        HasLanguageComp sig ctx elseBranch ty elseEffect →
        HasLanguageComp sig ctx (.ite condition thenBranch elseBranch) ty
          (EffectLanguage.join thenEffect elseEffect)
    | case : HasLanguageVal sig ctx scrutinee (.sum leftTy rightTy) →
        HasLanguageComp sig (leftTy :: ctx) leftBranch resultTy leftEffect →
        HasLanguageComp sig (rightTy :: ctx) rightBranch resultTy rightEffect →
        HasLanguageComp sig ctx (.case scrutinee leftBranch rightBranch) resultTy
          (EffectLanguage.join leftEffect rightEffect)
    | baseOp : sig.base operation = some ⟨parameterTy, responseTy⟩ →
        HasLanguageVal sig ctx parameter parameterTy →
        HasLanguageComp sig ctx (.baseOp operation parameter) responseTy
          (principal [EffectAtom.base operation])
    | freeOp : sig.free interface operation = some ⟨parameterTy, responseTy⟩ →
        HasLanguageVal sig ctx parameter parameterTy →
        HasLanguageComp sig ctx (.freeOp interface operation parameter) responseTy
          (principal [EffectAtom.free interface])
    | subeffect : HasLanguageComp sig ctx term ty lower → lower ≤ upper →
        HasLanguageComp sig ctx term ty upper
end

end EffectSemantics
