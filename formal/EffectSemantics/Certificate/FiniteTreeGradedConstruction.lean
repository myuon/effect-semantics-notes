import EffectSemantics.Certificate.GradedPackageFunctor
import EffectSemantics.Certificate.GenericFreeExtension

namespace EffectSemantics

/-!
# A constructed witness for the abstract graded package

The package theorem does not create extensions from no data.  This file gives
the canonical finite-tree witness: for the one-point grade algebra, every pair
of typed algebraic signatures has an initial free carrier, a coherent old-base
action, and hence an `ExtensibleGradedPackage`.
-/

/-- The one-point ordered effect algebra.  It is the ungraded special case of
the abstract graded theorem. -/
def trivialGradeAlgebra : GradeAlgebra where
  Grade := Unit
  one := ()
  mul := fun _ _ => ()
  le := fun _ _ => True
  leRefl := by intros; trivial
  leTrans := by intros; trivial

/-- A finite operation tree, viewed as a model over the one-point grade
algebra. -/
def finiteTreeModel (base free : OperationSignature) :
    GradedMonadModel trivialGradeAlgebra where
  T := fun _ α => FreeExtension base free α
  map := FreeExtension.map
  pure := FreeExtension.ret
  bind := FreeExtension.bind
  weaken := fun _ tree => tree
  strength := fun value =>
    FreeExtension.map (fun result => (value.1, result)) value.2
  map_id := FreeExtension.map_id
  map_comp := FreeExtension.map_comp

/-- Naturality of the canonical inclusion of old trees. -/
theorem FreeExtension.embedBase_map (function : α → β)
    (tree : FreeExtension.BaseTree base α) :
    FreeExtension.embedBase (free := free) (FreeExtension.map function tree) =
      FreeExtension.map function (FreeExtension.embedBase (free := free) tree) := by
  simp only [FreeExtension.map]
  rw [FreeExtension.embedBase_bind]
  congr

/-- The old finite-tree model embeds as a strong graded-model morphism. -/
def finiteTreeEmbedding (base free : OperationSignature) :
    GradedMonadMorphism (finiteTreeModel base OperationSignature.empty)
      (finiteTreeModel base free) where
  map := FreeExtension.embedBase
  natural := by intros; exact FreeExtension.embedBase_map _ _
  pure := by intros; rfl
  bind := by intros; exact FreeExtension.embedBase_bind _ _
  weaken := by intros; rfl
  strength := by intros; exact FreeExtension.embedBase_map _ _

/-- Flatten an old base tree whose leaves are already extended computations.
This is the concrete `baseAct` required by the abstract theorem. -/
def FreeExtension.baseAct
    (tree : FreeExtension.BaseTree base (FreeExtension base free α)) :
    FreeExtension base free α :=
  match tree with
  | .ret continuation => continuation
  | .baseOp operation continuation =>
      .baseOp operation (fun response => baseAct (continuation response))
  | .freeOp operation _ => Empty.elim operation

@[simp] theorem FreeExtension.baseAct_ret
    (tree : FreeExtension base free α) :
    baseAct (.ret tree : BaseTree base (FreeExtension base free α)) = tree := rfl

/-- `baseAct` is natural in the returned value. -/
theorem FreeExtension.baseAct_map (function : α → β)
    (tree : BaseTree base (FreeExtension base free α)) :
    baseAct (map (map function) tree) = map function (baseAct tree) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [map, bind, baseAct]
      congr
      funext response
      exact ih response
  | freeOp operation _ => exact Empty.elim operation

/-- Algebra multiplication law for the old-base action. -/
theorem FreeExtension.baseAct_mult
    (tree : BaseTree base (BaseTree base (FreeExtension base free α))) :
    baseAct (tree.bind id) = baseAct (map baseAct tree) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [bind, map, baseAct]
      congr
      funext response
      exact ih response
  | freeOp operation _ => exact Empty.elim operation

/-- The two action equations used in the paper proof, now for the canonical
finite-tree construction. -/
structure FiniteTreeActionCert (base free : OperationSignature) : Prop where
  unit : ∀ {α} (tree : FreeExtension base free α),
    FreeExtension.baseAct
      (.ret tree : FreeExtension.BaseTree base (FreeExtension base free α)) = tree
  natural : ∀ {α β} (function : α → β)
      (tree : FreeExtension.BaseTree base (FreeExtension base free α)),
    FreeExtension.baseAct
      (FreeExtension.map (FreeExtension.map function) tree) =
      FreeExtension.map function (FreeExtension.baseAct tree)
  multiplication : ∀ {α}
      (tree : FreeExtension.BaseTree base
        (FreeExtension.BaseTree base (FreeExtension base free α))),
    FreeExtension.baseAct (tree.bind id) =
      FreeExtension.baseAct (FreeExtension.map FreeExtension.baseAct tree)

theorem finiteTreeActionCert (base free : OperationSignature) :
    FiniteTreeActionCert base free where
  unit := FreeExtension.baseAct_ret
  natural := FreeExtension.baseAct_map
  multiplication := FreeExtension.baseAct_mult

/-- Every pair of typed finite algebraic signatures constructs an actual
object of the abstract package category. -/
def finiteTreeExtensiblePackage (base free : OperationSignature) :
    ExtensibleGradedPackage trivialGradeAlgebra where
  base := finiteTreeModel base OperationSignature.empty
  extended := finiteTreeModel base free
  embed := finiteTreeEmbedding base free
  baseAct := FreeExtension.baseAct

/-- An algebra map out of the free carrier is determined by its return and
operation equations. -/
structure GenericExtensionAlgebra.StructuralMap
    (algebra : GenericExtensionAlgebra base free carrier) where
  map : ∀ {α}, FreeExtension base free α → carrier α
  ret : ∀ {α} (value : α), map (.ret value) = algebra.monad.pure value
  baseOp : ∀ {α} (operation : base.Op)
      (continuation : base.Response operation → FreeExtension base free α),
    map (.baseOp operation continuation) =
      algebra.interpretBase operation (fun response => map (continuation response))
  freeOp : ∀ {α} (operation : free.Op)
      (continuation : free.Response operation → FreeExtension base free α),
    map (.freeOp operation continuation) =
      algebra.interpretFree operation (fun response => map (continuation response))

/-- Initiality/uniqueness of the finite free carrier. -/
theorem GenericExtensionAlgebra.StructuralMap.unique
    {base free : OperationSignature} {carrier : Type → Type}
    {algebra : GenericExtensionAlgebra base free carrier}
    (candidate : GenericExtensionAlgebra.StructuralMap algebra)
    (tree : FreeExtension base free α) :
    candidate.map tree = algebra.fold (base := base) (free := free) tree := by
  induction tree with
  | ret value => exact candidate.ret value
  | baseOp operation continuation ih =>
      rw [candidate.baseOp, GenericExtensionAlgebra.fold]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      rw [candidate.freeOp, GenericExtensionAlgebra.fold]
      congr
      funext response
      exact ih response

end EffectSemantics
