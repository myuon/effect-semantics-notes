import EffectSemantics.Metatheory.LanguageHandlerProgress
import EffectSemantics.Recursive.FlatApproximation
import EffectSemantics.Recursive.FlatApproximationTransport

namespace EffectSemantics

/-!
# Generic recursive language-extension package

This module states the base-independent recursive structure-preservation
theorem and the separate morphism and logical-relation lifting principles.
-/

/-- Non-circular conditions required from an arbitrary recursive base
observation.  `finiteAdequacy` speaks only about finite functional iterates;
the completed semantics and its fundamental property are derived below. -/
structure LanguageRecursiveModel (sig : LanguageSignature)
    (Outcome : Type) where
  functional : FlatApproximation.Carrier RecLanguageComp Outcome →
    FlatApproximation.Carrier RecLanguageComp Outcome
  continuous : FlatApproximation.OmegaContinuous functional
  Runs : RecLanguageComp → Outcome → Prop
  finiteAdequacy : ∀ {term outcome}, Runs term outcome ↔
    ∃ fuel, FlatApproximation.iterate functional fuel term = some outcome
  pole : RecLanguageComp → Outcome → Prop
  layerPreservesPole : ∀ approximation,
    FlatApproximation.Satisfies pole approximation →
    FlatApproximation.Satisfies pole (functional approximation)

namespace LanguageRecursiveModel

noncomputable def semantics (cert : LanguageRecursiveModel sig Outcome) :
    FlatApproximation.Carrier RecLanguageComp Outcome :=
  FlatApproximation.lfp cert.functional cert.continuous

/-- Abstract recursive structure-preservation theorem.  Any base satisfying
the local finite-iterate and one-layer pole obligations inherits a least
fixed-point model, operational adequacy and the recursive fundamental pole. -/
theorem main (cert : LanguageRecursiveModel sig Outcome) :
    (cert.functional cert.semantics = cert.semantics) ∧
    (∀ {candidate}, FlatApproximation.LE (cert.functional candidate) candidate →
      FlatApproximation.LE cert.semantics candidate) ∧
    (∀ {term outcome}, cert.Runs term outcome ↔
      cert.semantics term = some outcome) ∧
    FlatApproximation.Satisfies cert.pole cert.semantics := by
  refine ⟨FlatApproximation.lfp_unfold cert.continuous,
    fun prefixed => FlatApproximation.lfp_le_prefixed cert.continuous prefixed,
    ?_, ?_⟩
  · intro term outcome
    rw [cert.finiteAdequacy]
    exact (FlatApproximation.lfp_some_iff cert.continuous).symm
  · apply FlatApproximation.lfp_induction cert.continuous
      (FlatApproximation.satisfies_admissible cert.pole)
      (FlatApproximation.Satisfies.bottom cert.pole)
    exact cert.layerPreservesPole

end LanguageRecursiveModel

/-- Local commutation obligation for lifting a base outcome morphism through
recursive completion. -/
structure LanguageRecursiveMorphism
    (source : LanguageRecursiveModel sig Source)
    (target : LanguageRecursiveModel sig Target)
    (transform : Source → Target) : Prop where
  oneLayer : ∀ approximation,
    FlatApproximation.mapOutcome transform
        (source.functional approximation) =
      target.functional (FlatApproximation.mapOutcome transform approximation)

theorem LanguageRecursiveMorphism.lift
    (cert : LanguageRecursiveMorphism source target transform) :
    FlatApproximation.mapOutcome transform source.semantics = target.semantics :=
  FlatApproximation.lfp_mapOutcome source.continuous target.continuous
    cert.oneLayer

/-- Local binary-relation obligations for lifting a logical relation through
recursive completion. -/
structure LanguageRecursiveRelation
    (left : LanguageRecursiveModel sig Left)
    (right : LanguageRecursiveModel sig Right)
    (relation : FlatApproximation.Carrier RecLanguageComp Left →
      FlatApproximation.Carrier RecLanguageComp Right → Prop) : Prop where
  admissible : FlatApproximation.BinaryAdmissible relation
  bottom : relation FlatApproximation.bottom FlatApproximation.bottom
  oneLayer : ∀ {leftApprox rightApprox},
    relation leftApprox rightApprox →
    relation (left.functional leftApprox) (right.functional rightApprox)

theorem LanguageRecursiveRelation.lift
    (cert : LanguageRecursiveRelation left right relation) :
    relation left.semantics right.semantics :=
  FlatApproximation.lfp_relation left.continuous right.continuous
    cert.admissible cert.bottom cert.oneLayer

end EffectSemantics
