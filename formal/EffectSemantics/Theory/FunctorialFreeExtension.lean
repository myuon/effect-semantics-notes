import EffectSemantics.Theory.GenericFreeExtension

namespace EffectSemantics

/-!
# Functorial finite free-effect extension

This file packages the previously separate Type-level laws into a single
checked package.  It is intentionally concrete: objects are typed
operation signatures and arrows are response-preserving signature morphisms.
The more general graded/categorical theorem in the notes additionally assumes
the stated initial algebras and coherent base actions.
-/

open FreeExtension

/-- A pointwise presentation of the functor laws for the finite free carrier,
together with its monadic and relational compatibility. -/
structure FunctorialFreeExtension where
  identity : ∀ {base free : OperationSignature} {α : Type}
      (tree : FreeExtension base free α),
    mapSignature (SignatureMorphism.id base) (SignatureMorphism.id free)
      id tree = tree
  composition : ∀ {base₁ base₂ base₃ free₁ free₂ free₃ :
      OperationSignature} {α β γ : Type}
      (baseFirst : SignatureMorphism base₁ base₂)
      (baseSecond : SignatureMorphism base₂ base₃)
      (freeFirst : SignatureMorphism free₁ free₂)
      (freeSecond : SignatureMorphism free₂ free₃)
      (first : α → β) (second : β → γ)
      (tree : FreeExtension base₁ free₁ α),
    mapSignature baseSecond freeSecond second
        (mapSignature baseFirst freeFirst first tree) =
      mapSignature (baseSecond.comp baseFirst) (freeSecond.comp freeFirst)
        (second ∘ first) tree
  bindNatural : ∀ {base₁ base₂ free₁ free₂ : OperationSignature}
      {α β : Type}
      (baseMap : SignatureMorphism base₁ base₂)
      (freeMap : SignatureMorphism free₁ free₂)
      (valueMap : β → γ) (tree : FreeExtension base₁ free₁ α)
      (next : α → FreeExtension base₁ free₁ β),
    mapSignature baseMap freeMap valueMap (tree.bind next) =
      (mapSignature baseMap freeMap id tree).bind
        (fun value => mapSignature baseMap freeMap valueMap (next value))
  graphExact : ∀ {base₁ base₂ free₁ free₂ : OperationSignature}
      {α β : Type}
      (baseMap : SignatureMorphism base₁ base₂)
      (freeMap : SignatureMorphism free₁ free₂)
      (valueMap : α → β) (tree : FreeExtension base₁ free₁ α)
      (target : FreeExtension base₂ free₂ β),
    Rel baseMap.graph freeMap.graph
        (fun left right => valueMap left = right) tree target ↔
      mapSignature baseMap freeMap valueMap tree = target
  monad : ∀ base free, MonadStructure (FreeExtension base free)
  structuralRelator : ∀ base free,
    MonadRelator (FreeExtension base free) (monad base free)
  shallowValueNatural : ∀ {base free : OperationSignature} {α β : Type}
      (handler : FreeExtension.AffineHandler base free) (function : α → β)
      (tree : FreeExtension base free α),
    map function (shallow handler tree) = shallow handler (map function tree)
  shallowStructural : ∀ {base free : OperationSignature} {α β : Type}
      {relation : α → β → Prop}
      {left : FreeExtension base free α} {right : FreeExtension base free β},
    Rel (SignatureRelation.identity base) (SignatureRelation.identity free)
      relation left right →
    ∀ handler : FreeExtension.AffineHandler base free,
      Rel (SignatureRelation.identity base)
      (SignatureRelation.identity free) relation
      (shallow handler left) (shallow handler right)

/-- The finite free-effect carrier is functorial on base/free signatures and
values; its arrow action preserves bind, and structural graph lifting agrees
exactly with that arrow action. -/
def functorialFreeExtension : FunctorialFreeExtension where
  identity := mapSignature_id
  composition := mapSignature_comp
  bindNatural := fun baseMap freeMap valueMap tree next =>
    mapSignature_bind (valueMap := valueMap) baseMap freeMap tree next
  graphExact := fun baseMap freeMap valueMap tree target =>
    Rel.graphMapSignature_iff (baseMap := baseMap) (freeMap := freeMap)
      (valueMap := valueMap) (tree := tree) (target := target)
  monad := genericFreeMonad
  structuralRelator := genericFreeRelator
  shallowValueNatural := shallow_map
  shallowStructural := fun related handler => related.shallow handler

/-- Adequacy transport is the fold-naturality component of the same finite
extension: an observation morphism commuting with every layer commutes with
the unique structural fold. -/
theorem functorialFreeExtension_adequacyTransport
    {base free : OperationSignature}
    {denotation outcome : Type → Type}
    {denotational : GenericExtensionAlgebra base free denotation}
    {operational : GenericExtensionAlgebra base free outcome}
    (cert : GenericExtensionAlgebra.AdequacyAssumptions denotational operational)
    (tree : FreeExtension base free α) :
    cert.observe.map
        (denotational.fold (base := base) (free := free) tree) =
      operational.fold (base := base) (free := free) tree :=
  cert.lift tree

end EffectSemantics
