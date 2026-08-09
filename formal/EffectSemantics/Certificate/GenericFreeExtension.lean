import EffectSemantics.Certificate.BaseModels
import EffectSemantics.Denotational.GenericFreeExtension

namespace EffectSemantics

/-!
# Certificate extracted from the generic free extension

The construction is not merely a family of datatypes: it uniformly supplies
the finite monad and structural-relator certificates used by the preservation
development.
-/

def genericFreeMonadCert (base free : OperationSignature) :
    FiniteMonadCert (FreeExtension base free) where
  pure := FreeExtension.ret
  bind := FreeExtension.bind
  leftUnit := fun _ _ => rfl
  rightUnit := FreeExtension.bind_ret
  associative := FreeExtension.bind_assoc

def genericFreeRelatorCert (base free : OperationSignature) :
    FiniteRelatorCert (FreeExtension base free) (genericFreeMonadCert base free) where
  Rel := FreeExtension.Rel (FreeExtension.SignatureRelation.identity base)
    (FreeExtension.SignatureRelation.identity free)
  reflEq := FreeExtension.Rel.reflEq
  bindClosed := FreeExtension.Rel.bind

/-- Finite abstract structure-preservation certificate: adjoining any typed
free signature preserves monad laws, embeds the old base carrier injectively,
and equips the result with a bind-compatible structural relation. -/
structure GenericFreeExtensionCert (base free : OperationSignature) where
  monad : FiniteMonadCert (FreeExtension base free)
  relator : FiniteRelatorCert (FreeExtension base free) monad
  baseEmbeddingRetraction : ∀ {α} (tree : FreeExtension.BaseTree base α),
    FreeExtension.eraseFree
      (FreeExtension.embedBase (free := free) tree)
      (FreeExtension.embedBase_baseOnly tree) = tree
  baseEmbeddingBind : ∀ {α β} (tree : FreeExtension.BaseTree base α)
      (next : α → FreeExtension.BaseTree base β),
    FreeExtension.embedBase (free := free) (tree.bind next) =
      (FreeExtension.embedBase (free := free) tree).bind
        (fun value => FreeExtension.embedBase (free := free) (next value))
  shallowNatural : ∀ {α β} (handler : FreeExtension.AffineHandler base free)
      (function : α → β) (tree : FreeExtension base free α),
    FreeExtension.map function (FreeExtension.shallow handler tree) =
      FreeExtension.shallow handler (FreeExtension.map function tree)
  shallowRelation : ∀ {α β} {relation : α → β → Prop}
      {left : FreeExtension base free α} {right : FreeExtension base free β},
    FreeExtension.Rel (FreeExtension.SignatureRelation.identity base)
      (FreeExtension.SignatureRelation.identity free) relation left right →
    ∀ handler, FreeExtension.Rel (FreeExtension.SignatureRelation.identity base)
      (FreeExtension.SignatureRelation.identity free) relation
      (FreeExtension.shallow handler left) (FreeExtension.shallow handler right)

def genericFreeExtensionStructurePreservation (base free : OperationSignature) :
    GenericFreeExtensionCert base free where
  monad := genericFreeMonadCert base free
  relator := genericFreeRelatorCert base free
  baseEmbeddingRetraction := FreeExtension.eraseFree_embedBase
  baseEmbeddingBind := FreeExtension.embedBase_bind
  shallowNatural := FreeExtension.shallow_map
  shallowRelation := fun related handler => related.shallow handler

/-- A model of both old and newly adjoined operations in a target monad.
The two distributivity laws are precisely what makes structural folding
compatible with sequencing. -/
structure GenericExtensionAlgebra (base free : OperationSignature)
    (carrier : Type → Type) where
  monad : FiniteMonadCert carrier
  interpretBase : ∀ {α} (operation : base.Op),
    (base.Response operation → carrier α) → carrier α
  interpretFree : ∀ {α} (operation : free.Op),
    (free.Response operation → carrier α) → carrier α
  baseBind : ∀ {α β} (operation : base.Op)
      (continuation : base.Response operation → carrier α)
      (next : α → carrier β),
    monad.bind (interpretBase operation continuation) next =
      interpretBase operation (fun response => monad.bind (continuation response) next)
  freeBind : ∀ {α β} (operation : free.Op)
      (continuation : free.Response operation → carrier α)
      (next : α → carrier β),
    monad.bind (interpretFree operation continuation) next =
      interpretFree operation (fun response => monad.bind (continuation response) next)

namespace GenericExtensionAlgebra

def fold (algebra : GenericExtensionAlgebra base free carrier) :
    FreeExtension base free α → carrier α
  | .ret value => algebra.monad.pure value
  | .baseOp operation continuation =>
      algebra.interpretBase operation (fun response =>
        algebra.fold (continuation response))
  | .freeOp operation continuation =>
      algebra.interpretFree operation (fun response =>
        algebra.fold (continuation response))

@[simp] theorem fold_ret (algebra : GenericExtensionAlgebra base free carrier)
    (value : α) : algebra.fold (.ret value) = algebra.monad.pure value := rfl

theorem fold_bind (algebra : GenericExtensionAlgebra base free carrier)
    (tree : FreeExtension base free α) (next : α → FreeExtension base free β) :
    algebra.fold (tree.bind next) =
      algebra.monad.bind (algebra.fold tree) (fun value => algebra.fold (next value)) := by
  induction tree with
  | ret value => symm; exact algebra.monad.leftUnit value _
  | baseOp operation continuation ih =>
      rw [fold, algebra.baseBind]
      simp only [FreeExtension.bind, fold]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      rw [fold, algebra.freeBind]
      simp only [FreeExtension.bind, fold]
      congr
      funext response
      exact ih response

/-- A monad morphism that also commutes with interpretations of every old and
new operation. -/
structure Morphism
    (source : GenericExtensionAlgebra base free sourceCarrier)
    (target : GenericExtensionAlgebra base free targetCarrier) where
  map : ∀ {α}, sourceCarrier α → targetCarrier α
  pure : ∀ {α} (value : α), map (source.monad.pure value) = target.monad.pure value
  bind : ∀ {α β} (tree : sourceCarrier α) (next : α → sourceCarrier β),
    map (source.monad.bind tree next) =
      target.monad.bind (map tree) (fun value => map (next value))
  preservesBase : ∀ {α} (operation : base.Op)
      (continuation : base.Response operation → sourceCarrier α),
    map (source.interpretBase operation continuation) =
      target.interpretBase operation (fun response => map (continuation response))
  preservesFree : ∀ {α} (operation : free.Op)
      (continuation : free.Response operation → sourceCarrier α),
    map (source.interpretFree operation continuation) =
      target.interpretFree operation (fun response => map (continuation response))

/-- Monad morphisms lift through the entire free extension by commuting with
its unique structural fold. -/
theorem Morphism.lift
    {base free : OperationSignature}
    {sourceCarrier targetCarrier : Type → Type}
    {source : GenericExtensionAlgebra base free sourceCarrier}
    {target : GenericExtensionAlgebra base free targetCarrier}
    (morphism : Morphism source target)
    (tree : FreeExtension base free α) :
    morphism.map (source.fold (base := base) (free := free) tree) =
      target.fold (base := base) (free := free) tree := by
  induction tree with
  | ret value => exact morphism.pure value
  | baseOp operation continuation ih =>
      rw [fold, morphism.preservesBase, fold]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      rw [fold, morphism.preservesFree, fold]
      congr
      funext response
      exact ih response

/-- Local clauses sufficient to lift a heterogeneous logical relation through
the free extension. -/
structure Relation
    (left : GenericExtensionAlgebra base free leftCarrier)
    (right : GenericExtensionAlgebra base free rightCarrier)
    (rel : ∀ {α}, leftCarrier α → rightCarrier α → Prop) where
  pure : ∀ {α} (value : α), rel (left.monad.pure value) (right.monad.pure value)
  preservesBase : ∀ {α} (operation : base.Op)
      (leftContinuation : base.Response operation → leftCarrier α)
      (rightContinuation : base.Response operation → rightCarrier α),
    (∀ response, rel (leftContinuation response) (rightContinuation response)) →
    rel (left.interpretBase operation leftContinuation)
      (right.interpretBase operation rightContinuation)
  preservesFree : ∀ {α} (operation : free.Op)
      (leftContinuation : free.Response operation → leftCarrier α)
      (rightContinuation : free.Response operation → rightCarrier α),
    (∀ response, rel (leftContinuation response) (rightContinuation response)) →
    rel (left.interpretFree operation leftContinuation)
      (right.interpretFree operation rightContinuation)

/-- A relation preserved by return and each one-layer operation relates the
two folds of every finite extended computation. -/
theorem Relation.lift
    {base free : OperationSignature}
    {leftCarrier rightCarrier : Type → Type}
    {left : GenericExtensionAlgebra base free leftCarrier}
    {right : GenericExtensionAlgebra base free rightCarrier}
    {rel : ∀ {α}, leftCarrier α → rightCarrier α → Prop}
    (relation : Relation left right rel)
    (tree : FreeExtension base free α) :
    rel (left.fold (base := base) (free := free) tree)
      (right.fold (base := base) (free := free) tree) := by
  induction tree with
  | ret value => exact relation.pure value
  | baseOp operation continuation ih => exact relation.preservesBase operation _ _ ih
  | freeOp operation continuation ih => exact relation.preservesFree operation _ _ ih

/-- A heterogeneous family of observations used to define a genuine
TT-lifting between two target models. -/
structure Observation
    (leftCarrier rightCarrier : Type → Type) where
  relates : ∀ {α β}, (α → β → Prop) → leftCarrier α → rightCarrier β → Prop

def Orthogonal
    (observation : Observation leftCarrier rightCarrier)
    (valueRel : α → β → Prop)
    (resultRel : γ → δ → Prop)
    (leftContext : α → leftCarrier γ)
    (rightContext : β → rightCarrier δ) : Prop :=
  ∀ {leftValue rightValue}, valueRel leftValue rightValue →
    observation.relates resultRel
      (leftContext leftValue) (rightContext rightValue)

/-- Biorthogonal closure of a value relation against the selected observation
family and the two target monads. -/
def TT
    (left : GenericExtensionAlgebra base free leftCarrier)
    (right : GenericExtensionAlgebra base free rightCarrier)
    (observation : Observation leftCarrier rightCarrier)
    (valueRel : α → β → Prop)
    (leftTree : leftCarrier α) (rightTree : rightCarrier β) : Prop :=
  ∀ {γ δ} (resultRel : γ → δ → Prop)
      (leftContext : α → leftCarrier γ)
      (rightContext : β → rightCarrier δ),
    Orthogonal observation valueRel resultRel leftContext rightContext →
    observation.relates resultRel
      (left.monad.bind leftTree leftContext)
      (right.monad.bind rightTree rightContext)

theorem TT.pure
    (related : valueRel leftValue rightValue) :
    TT left right observation valueRel
      (left.monad.pure leftValue) (right.monad.pure rightValue) := by
  intro γ δ resultRel leftContext rightContext contexts
  rw [left.monad.leftUnit, right.monad.leftUnit]
  exact contexts related

/-- Local TT obligations for old and new operation layers.  These are the
observation-sensitive premises that cannot be obtained from monad laws alone. -/
structure TTLayerCert
    (left : GenericExtensionAlgebra base free leftCarrier)
    (right : GenericExtensionAlgebra base free rightCarrier)
    (observation : Observation leftCarrier rightCarrier) where
  preservesBase : ∀ {α β} (valueRel : α → β → Prop)
      (operation : base.Op)
      (leftContinuation : base.Response operation → leftCarrier α)
      (rightContinuation : base.Response operation → rightCarrier β),
    (∀ response, TT left right observation valueRel
      (leftContinuation response) (rightContinuation response)) →
    TT left right observation valueRel
      (left.interpretBase operation leftContinuation)
      (right.interpretBase operation rightContinuation)
  preservesFree : ∀ {α β} (valueRel : α → β → Prop)
      (operation : free.Op)
      (leftContinuation : free.Response operation → leftCarrier α)
      (rightContinuation : free.Response operation → rightCarrier β),
    (∀ response, TT left right observation valueRel
      (leftContinuation response) (rightContinuation response)) →
    TT left right observation valueRel
      (left.interpretFree operation leftContinuation)
      (right.interpretFree operation rightContinuation)

/-- Structural free-extension relations are contained in the TT-lifting as
soon as each one-layer operation interpretation preserves TT. -/
theorem TTLayerCert.lift
    {base free : OperationSignature}
    {leftCarrier rightCarrier : Type → Type}
    {left : GenericExtensionAlgebra base free leftCarrier}
    {right : GenericExtensionAlgebra base free rightCarrier}
    {observation : Observation leftCarrier rightCarrier}
    {α β : Type} {valueRel : α → β → Prop}
    {leftTree : FreeExtension base free α}
    {rightTree : FreeExtension base free β}
    (cert : TTLayerCert left right observation)
    (treeRel : FreeExtension.Rel
      (FreeExtension.SignatureRelation.identity base)
      (FreeExtension.SignatureRelation.identity free)
      valueRel leftTree rightTree) :
    TT left right observation valueRel
      (left.fold (base := base) (free := free) leftTree)
      (right.fold (base := base) (free := free) rightTree) := by
  induction treeRel with
  | ret related => exact TT.pure related
  | baseOp operations continuations ih =>
      subst operations
      exact cert.preservesBase _ _ _ _ (fun response => ih rfl)
  | freeOp operations continuations ih =>
      subst operations
      exact cert.preservesFree _ _ _ _ (fun response => ih rfl)

end GenericExtensionAlgebra

end EffectSemantics
