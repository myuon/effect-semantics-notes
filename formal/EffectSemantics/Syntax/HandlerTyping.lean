import EffectSemantics.Operational.ShallowHandler
import EffectSemantics.Metatheory.RequestDecomposition

namespace EffectSemantics

/-- Local typing evidence for one affine operation clause. -/
structure TypedAffineClause (sig : Signature) (ctx : Context)
    (interface operation : Nat) (clause : Comp) (clauseEffect : Effect) where
  parameterTy : Ty
  responseTy : Ty
  signatureLookup : sig.free interface operation =
    some ⟨parameterTy, responseTy⟩
  bodyTyping : HasComp sig (parameterTy :: ctx) clause responseTy clauseEffect

/-- The syntactic part of the affine handler certificate.  It deliberately
does not yet claim an output-grade transformation: that requires the ordered
optionality and residual-context obligations isolated in Chapter III. -/
structure HasAffineHandler (sig : Signature) (ctx : Context)
    (interface : Nat) (handler : AffineHandler) (clauseEffect : Effect) where
  clauseTyping : ∀ {operation clause},
    handler.lookup operation = some clause →
    TypedAffineClause sig ctx interface operation clause clauseEffect

/-- Exhaustiveness is separate from ordinary handler typing.  Partial
handlers remain meaningful because missing clauses are transparently
forwarded. -/
def AffineHandler.Exhaustive (sig : Signature) (interface : Nat)
    (handler : AffineHandler) : Prop :=
  ∀ operation parameterTy responseTy,
    sig.free interface operation = some ⟨parameterTy, responseTy⟩ →
    ∃ clause, handler.lookup operation = some clause

def HasAffineHandler.typedClause
    (typing : HasAffineHandler sig ctx interface handler clauseEffect)
    (found : handler.lookup operation = some clause) :
    TypedAffineClause sig ctx interface operation clause clauseEffect :=
  typing.clauseTyping found

/-- Substituting the runtime operation parameter into a typed affine clause
produces a response computation in the surrounding context. -/
def HasAffineHandler.instantiate
    (typing : HasAffineHandler sig ctx interface handler clauseEffect)
    (found : handler.lookup operation = some clause)
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (parameterTyping : HasVal sig ctx parameter parameterTy) :
    HasComp sig ctx (clause.subst0 parameter) responseTy clauseEffect := by
  let typed := typing.typedClause found
  have signatureEq :
      OpDecl.mk typed.parameterTy typed.responseTy =
        OpDecl.mk parameterTy responseTy := by
    exact Option.some.inj (typed.signatureLookup.symm.trans lookup)
  cases signatureEq
  exact typed.bodyTyping.subst0_preserved parameterTyping

end EffectSemantics
