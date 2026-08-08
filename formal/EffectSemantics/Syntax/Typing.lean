import EffectSemantics.Syntax.Term

namespace EffectSemantics

mutual
  /-- Extrinsic value typing. -/
  inductive HasVal (sig : Signature) : Context → Val → Ty → Type where
    | var : Context.lookup ctx index = some ty →
        HasVal sig ctx (.var index) ty
    | unit : HasVal sig ctx .unit .unit
    | bool : HasVal sig ctx (.bool value) .bool
    | pair : HasVal sig ctx left leftTy → HasVal sig ctx right rightTy →
        HasVal sig ctx (.pair left right) (.prod leftTy rightTy)
    | inl : HasVal sig ctx value leftTy →
        HasVal sig ctx (.inl value rightTy) (.sum leftTy rightTy)
    | inr : HasVal sig ctx value rightTy →
        HasVal sig ctx (.inr leftTy value) (.sum leftTy rightTy)
    | lam : HasComp sig (domain :: ctx) body codomain latent →
        HasVal sig ctx (.lam domain latent body) (.arr domain latent codomain)

  /-- Extrinsic computation typing with an ordered may-effect upper bound. -/
  inductive HasComp (sig : Signature) : Context → Comp → Ty → Effect → Type where
    | ret : HasVal sig ctx value ty →
        HasComp sig ctx (.ret value) ty 1
    | letE : HasComp sig ctx bound boundTy boundEffect →
        HasComp sig (boundTy :: ctx) body resultTy bodyEffect →
        HasComp sig ctx (.letE bound body) resultTy (boundEffect * bodyEffect)
    | app : HasVal sig ctx function (.arr domain latent codomain) →
        HasVal sig ctx argument domain →
        HasComp sig ctx (.app function argument) codomain latent
    | ite : HasVal sig ctx condition .bool →
        HasComp sig ctx thenBranch ty effect →
        HasComp sig ctx elseBranch ty effect →
        HasComp sig ctx (.ite condition thenBranch elseBranch) ty effect
    | case : HasVal sig ctx scrutinee (.sum leftTy rightTy) →
        HasComp sig (leftTy :: ctx) leftBranch resultTy effect →
        HasComp sig (rightTy :: ctx) rightBranch resultTy effect →
        HasComp sig ctx (.case scrutinee leftBranch rightBranch) resultTy effect
    | baseOp : sig.base operation = some ⟨parameterTy, responseTy⟩ →
        HasVal sig ctx parameter parameterTy →
        HasComp sig ctx (.baseOp operation parameter) responseTy
          [EffectAtom.base operation]
    | freeOp : sig.free interface operation = some ⟨parameterTy, responseTy⟩ →
        HasVal sig ctx parameter parameterTy →
        HasComp sig ctx (.freeOp interface operation parameter) responseTy
          [EffectAtom.free interface]
    | subeffect : HasComp sig ctx term ty lower → lower ≤ upper →
        HasComp sig ctx term ty upper
end

mutual
  def HasVal.height : HasVal sig ctx value ty → Nat
    | .var _ => 1
    | .unit => 1
    | .bool => 1
    | .pair left right => Nat.max left.height right.height + 1
    | .inl value => value.height + 1
    | .inr value => value.height + 1
    | .lam body => body.height + 1

  def HasComp.height : HasComp sig ctx term ty effect → Nat
    | .ret value => value.height + 1
    | .letE bound body => Nat.max bound.height body.height + 1
    | .app function argument => Nat.max function.height argument.height + 1
    | .ite condition thenBranch elseBranch =>
        Nat.max condition.height (Nat.max thenBranch.height elseBranch.height) + 1
    | .case scrutinee leftBranch rightBranch =>
        Nat.max scrutinee.height (Nat.max leftBranch.height rightBranch.height) + 1
    | .baseOp _ parameter => parameter.height + 1
    | .freeOp _ parameter => parameter.height + 1
    | .subeffect inner _ => inner.height + 1
end

namespace HasComp

def weakenEffect {sig : Signature} {ctx : Context} {term : Comp} {ty : Ty}
    {lower upper : Effect} (typing : HasComp sig ctx term ty lower)
    (bound : lower ≤ upper) : HasComp sig ctx term ty upper :=
  .subeffect typing bound

def optionalFree {sig : Signature} {ctx : Context} {term : Comp} {ty : Ty}
    (typing : HasComp sig ctx term ty 1) (interface : Nat) :
    HasComp sig ctx term ty [EffectAtom.free interface] :=
  typing.subeffect (Effect.optional_free interface)

end HasComp
end EffectSemantics
