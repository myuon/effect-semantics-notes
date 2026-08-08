import EffectSemantics.Recursive.StableObservationMorphism

namespace EffectSemantics
namespace StableObservation

/-- All data required to lift an outcome map through recursive least fixed
points.  No monad or category-level law is hidden in the package. -/
structure RecursiveMorphismCert
    (sourceFunction : StableObservation Source → StableObservation Source)
    (targetFunction : StableObservation Target → StableObservation Target)
    (transform : Source → Target) : Prop where
  sourceContinuous : OmegaContinuous sourceFunction
  targetContinuous : OmegaContinuous targetFunction
  commutes : ∀ observation,
    mapOutcome transform (sourceFunction observation) =
      targetFunction (mapOutcome transform observation)

theorem RecursiveMorphismCert.lift
    (cert : RecursiveMorphismCert sourceFunction targetFunction transform) :
    mapOutcome transform (lfp sourceFunction cert.sourceContinuous) =
      lfp targetFunction cert.targetContinuous :=
  mapOutcome_lfp transform cert.sourceContinuous cert.targetContinuous
    cert.commutes

/-- All data required to lift a binary logical relation through recursion. -/
structure RecursiveRelationCert
    (leftFunction : StableObservation Left → StableObservation Left)
    (rightFunction : StableObservation Right → StableObservation Right)
    (relation : StableObservation Left → StableObservation Right → Prop) : Prop where
  leftContinuous : OmegaContinuous leftFunction
  rightContinuous : OmegaContinuous rightFunction
  admissible : BinaryAdmissible relation
  bottomRelated : relation bottom bottom
  oneLayer : ∀ left right, relation left right →
    relation (leftFunction left) (rightFunction right)

theorem RecursiveRelationCert.lift
    (cert : RecursiveRelationCert leftFunction rightFunction relation) :
    relation (lfp leftFunction cert.leftContinuous)
      (lfp rightFunction cert.rightContinuous) :=
  lfp_related cert.leftContinuous cert.rightContinuous cert.admissible
    cert.bottomRelated cert.oneLayer

end StableObservation
end EffectSemantics
