namespace EffectSemantics

/-!
# Category of extensible graded packages

This file formalizes the categorical skeleton of the abstract extension
theorem.  The indexed initial-algebra construction remains an object-side
premise: an object contains its chosen extended carrier and base action.
-/

/-- The ordered multiplication used for effect grades.  Keeping it explicit
avoids imposing Lean type-class or definitional-equality requirements on a
paper-level effect algebra. -/
structure GradeAlgebra where
  Grade : Type
  one : Grade
  mul : Grade → Grade → Grade
  le : Grade → Grade → Prop
  leRefl : ∀ grade, le grade grade
  leTrans : le first second → le second third → le first third

/-- The operations of a strong graded model.  The laws involving grade
associativity and units belong to the object certificate; the functor proof
below only needs the grade-preserving functor laws recorded here. -/
structure GradedMonadModel (grades : GradeAlgebra) where
  T : grades.Grade → Type → Type
  map : (α → β) → T e α → T e β
  pure : α → T grades.one α
  bind : T e α → (α → T f β) → T (grades.mul e f) β
  weaken : grades.le e f → T e α → T f α
  strength : α × T e β → T e (α × β)
  map_id : ∀ (value : T e α), map id value = value
  map_comp : ∀ (first : α → β) (second : β → γ) (value : T e α),
    map second (map first value) = map (second ∘ first) value

/-- Strong graded-model morphisms, including coherent weakening. -/
structure GradedMonadMorphism
    (source target : GradedMonadModel grades) where
  map : ∀ {e α}, source.T e α → target.T e α
  natural : ∀ (function : α → β) (value : source.T e α),
    map (source.map function value) = target.map function (map value)
  pure : ∀ (value : α), map (source.pure value) = target.pure value
  bind : ∀ (value : source.T e α) (next : α → source.T f β),
    map (source.bind value next) =
      target.bind (map value) (fun x => map (next x))
  weaken : ∀ (bound : grades.le e f) (value : source.T e α),
    map (source.weaken bound value) = target.weaken bound (map value)
  strength : ∀ (value : α × source.T e β),
    map (source.strength value) =
      target.strength (value.1, map value.2)

namespace GradedMonadMorphism

@[ext] theorem ext (left right : GradedMonadMorphism source target)
    (equal : ∀ e α (value : source.T e α), left.map value = right.map value) :
    left = right := by
  cases left
  cases right
  congr
  funext e α value
  exact equal e α value

def id (model : GradedMonadModel grades) : GradedMonadMorphism model model where
  map := fun value => value
  natural := by intros; rfl
  pure := by intros; rfl
  bind := by intros; rfl
  weaken := by intros; rfl
  strength := by intros; rfl

def comp (second : GradedMonadMorphism middle target)
    (first : GradedMonadMorphism source middle) :
    GradedMonadMorphism source target where
  map value := second.map (first.map value)
  natural := by intros; rw [first.natural, second.natural]
  pure := by intros; rw [first.pure, second.pure]
  bind := by intros; rw [first.bind, second.bind]
  weaken := by intros; rw [first.weaken, second.weaken]
  strength := by intros; rw [first.strength, second.strength]

@[simp] theorem id_comp (morphism : GradedMonadMorphism source target) :
    comp (id target) morphism = morphism := by
  ext
  simp [comp, id]

@[simp] theorem comp_id (morphism : GradedMonadMorphism source target) :
    comp morphism (id source) = morphism := by
  ext
  simp [comp, id]

theorem comp_assoc (third : GradedMonadMorphism thirdModel fourth)
    (second : GradedMonadMorphism secondModel thirdModel)
    (first : GradedMonadMorphism firstModel secondModel) :
    comp third (comp second first) = comp (comp third second) first := by
  ext
  rfl

end GradedMonadMorphism

/-- A chosen indexed extension and its extra old-base action. -/
structure ExtensibleGradedPackage (grades : GradeAlgebra) where
  base : GradedMonadModel grades
  extended : GradedMonadModel grades
  embed : GradedMonadMorphism base extended
  baseAct : base.T b (extended.T d α) → extended.T (grades.mul b d) α

/-- Compatible package arrows.  `actSquare` is the explicit Act-Morphism
condition from the paper theorem. -/
structure ExtensibleGradedMorphism
    (source target : ExtensibleGradedPackage grades) where
  base : GradedMonadMorphism source.base target.base
  lifted : GradedMonadMorphism source.extended target.extended
  embedSquare : ∀ (value : source.base.T e α),
    lifted.map (source.embed.map value) = target.embed.map (base.map value)
  actSquare : ∀ (value : source.base.T b (source.extended.T d α)),
    lifted.map (source.baseAct value) =
      target.baseAct (target.base.map lifted.map (base.map value))

namespace ExtensibleGradedMorphism

@[ext] theorem ext (left right : ExtensibleGradedMorphism source target)
    (baseEq : left.base = right.base) (liftedEq : left.lifted = right.lifted) :
    left = right := by
  cases left
  cases right
  simp_all

def id (package : ExtensibleGradedPackage grades) :
    ExtensibleGradedMorphism package package where
  base := GradedMonadMorphism.id package.base
  lifted := GradedMonadMorphism.id package.extended
  embedSquare := by intros; rfl
  actSquare := by
    intros
    simp only [GradedMonadMorphism.id]
    exact congrArg package.baseAct (package.base.map_id _).symm

def comp (second : ExtensibleGradedMorphism middle target)
    (first : ExtensibleGradedMorphism source middle) :
    ExtensibleGradedMorphism source target where
  base := GradedMonadMorphism.comp second.base first.base
  lifted := GradedMonadMorphism.comp second.lifted first.lifted
  embedSquare := by
    intros
    simp only [GradedMonadMorphism.comp]
    rw [first.embedSquare, second.embedSquare]
  actSquare := by
    intro b d α value
    simp only [GradedMonadMorphism.comp]
    rw [first.actSquare, second.actSquare, second.base.natural]
    rw [target.base.map_comp]
    rfl

@[simp] theorem id_comp (morphism : ExtensibleGradedMorphism source target) :
    comp (id target) morphism = morphism := by
  apply ext
  · exact GradedMonadMorphism.id_comp morphism.base
  · exact GradedMonadMorphism.id_comp morphism.lifted

@[simp] theorem comp_id (morphism : ExtensibleGradedMorphism source target) :
    comp morphism (id source) = morphism := by
  apply ext
  · exact GradedMonadMorphism.comp_id morphism.base
  · exact GradedMonadMorphism.comp_id morphism.lifted

theorem comp_assoc (third : ExtensibleGradedMorphism thirdPackage fourth)
    (second : ExtensibleGradedMorphism secondPackage thirdPackage)
    (first : ExtensibleGradedMorphism firstPackage secondPackage) :
    comp third (comp second first) = comp (comp third second) first := by
  apply ext <;> rfl

end ExtensibleGradedMorphism

/-- A small category record, avoiding a dependency on a universe-heavy
category library while retaining exactly the laws needed here. -/
structure PackageCategory where
  Obj : Type 1
  Hom : Obj → Obj → Type 1
  id : ∀ object, Hom object object
  comp : Hom middle target → Hom source middle → Hom source target
  id_comp : ∀ (morphism : Hom source target), comp (id target) morphism = morphism
  comp_id : ∀ (morphism : Hom source target), comp morphism (id source) = morphism
  assoc : ∀ (third : Hom c d) (second : Hom b c) (first : Hom a b),
    comp third (comp second first) = comp (comp third second) first

def gradedMonadCategory (grades : GradeAlgebra) : PackageCategory where
  Obj := GradedMonadModel grades
  Hom := GradedMonadMorphism
  id := GradedMonadMorphism.id
  comp := GradedMonadMorphism.comp
  id_comp := GradedMonadMorphism.id_comp
  comp_id := GradedMonadMorphism.comp_id
  assoc := GradedMonadMorphism.comp_assoc

def extensibleGradedPackageCategory (grades : GradeAlgebra) : PackageCategory where
  Obj := ExtensibleGradedPackage grades
  Hom := ExtensibleGradedMorphism
  id := ExtensibleGradedMorphism.id
  comp := ExtensibleGradedMorphism.comp
  id_comp := ExtensibleGradedMorphism.id_comp
  comp_id := ExtensibleGradedMorphism.comp_id
  assoc := ExtensibleGradedMorphism.comp_assoc

/-- Functors between the small package categories. -/
structure PackageFunctor (source target : PackageCategory) where
  obj : source.Obj → target.Obj
  map : source.Hom left right → target.Hom (obj left) (obj right)
  map_id : ∀ object, map (source.id object) = target.id (obj object)
  map_comp : ∀ (second : source.Hom middle right)
      (first : source.Hom left middle),
    map (source.comp second first) = target.comp (map second) (map first)

/-- Selecting the chosen extension and lifted arrow is a functor. -/
def gradedFreeExtensionFunctor (grades : GradeAlgebra) :
    PackageFunctor (extensibleGradedPackageCategory grades)
      (gradedMonadCategory grades) where
  obj package := package.extended
  map morphism := morphism.lifted
  map_id := by intros; rfl
  map_comp := by intros; rfl

end EffectSemantics
