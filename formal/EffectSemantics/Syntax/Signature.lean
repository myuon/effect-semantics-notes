import EffectSemantics.Syntax.Effect

namespace EffectSemantics

/-- Value types.  Function arrows carry the latent ordered computation
effect, matching the paper notation `A -(e)-> B`. -/
inductive Ty where
  | unit
  | bool
  | prod (left right : Ty)
  | sum (left right : Ty)
  | arr (domain : Ty) (latent : Effect) (codomain : Ty)
  deriving DecidableEq, Repr

structure OpDecl where
  parameter : Ty
  response : Ty
  deriving DecidableEq, Repr

/-- A base signature and a family of user-defined interface signatures.
Names are natural numbers in the first implementation; surface names are
notation only. -/
structure Signature where
  base : Nat → Option OpDecl
  free : Nat → Nat → Option OpDecl

namespace Signature

theorem base_lookup_unique {sig : Signature} {name : Nat} {d₁ d₂ : OpDecl}
    (h₁ : sig.base name = some d₁) (h₂ : sig.base name = some d₂) : d₁ = d₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem free_lookup_unique {sig : Signature} {interface operation : Nat}
    {d₁ d₂ : OpDecl}
    (h₁ : sig.free interface operation = some d₁)
    (h₂ : sig.free interface operation = some d₂) : d₁ = d₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Signature
end EffectSemantics
