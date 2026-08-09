import EffectSemantics.Certificate.LanguageFinite
import EffectSemantics.Recursive.FlatApproximation
import EffectSemantics.Recursive.FlatApproximationTransport

namespace EffectSemantics

/-- Base-independent syntax/effect part of the extension theorem. -/
structure LanguageSourceStructureCert (sig : LanguageSignature) where
  effects : LanguageEffectCert
  preservation : ∀ {term next ctx resultTy effect},
    LanguageStep term next → HasLanguageComp sig ctx term resultTy effect →
      HasLanguageComp sig ctx next resultTy effect
  progress : ∀ {term resultTy effect},
    HasLanguageComp sig [] term resultTy effect → LanguageProgress term
  handlerPreservation : ∀ {ctx interface handler replacement input resultTy
      state next},
    HasLanguageAffineHandler sig ctx interface handler replacement →
    LanguageShallowStep state next →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy
      state →
    HasLanguageHandlerState sig ctx interface handler replacement input resultTy
      next
  handlerProgress : ∀ {interface handler replacement input resultTy term},
    HasLanguageHandlerState sig [] interface handler replacement input resultTy
      (.shallow interface handler term) →
    LanguageShallowProgress (.shallow interface handler term)

def languageSourceStructureCert (sig : LanguageSignature) :
    LanguageSourceStructureCert sig where
  effects := languageEffectCert
  preservation := LanguageStep.preserve
  progress := HasLanguageComp.progressClosed
  handlerPreservation := fun handlerTyping step typing =>
    step.preserve handlerTyping typing
  handlerProgress := HasLanguageHandlerState.progressClosed

/-- Non-circular conditions required from an arbitrary recursive base
observation.  `finiteAdequacy` speaks only about finite functional iterates;
the completed semantics and its fundamental property are derived below. -/
structure LanguageRecursiveBaseCert (sig : LanguageSignature)
    (Outcome : Type) where
  source : LanguageSourceStructureCert sig
  functional : FlatApproximation.Carrier LanguageComp Outcome →
    FlatApproximation.Carrier LanguageComp Outcome
  continuous : FlatApproximation.OmegaContinuous functional
  Runs : LanguageComp → Outcome → Prop
  finiteAdequacy : ∀ {term outcome}, Runs term outcome ↔
    ∃ fuel, FlatApproximation.iterate functional fuel term = some outcome
  pole : LanguageComp → Outcome → Prop
  layerPreservesPole : ∀ approximation,
    FlatApproximation.Satisfies pole approximation →
    FlatApproximation.Satisfies pole (functional approximation)

namespace LanguageRecursiveBaseCert

noncomputable def semantics (cert : LanguageRecursiveBaseCert sig Outcome) :
    FlatApproximation.Carrier LanguageComp Outcome :=
  FlatApproximation.lfp cert.functional cert.continuous

/-- Abstract recursive structure-preservation theorem.  Any base satisfying
the local finite-iterate and one-layer pole obligations inherits a least
fixed-point model, operational adequacy and the recursive fundamental pole. -/
theorem main (cert : LanguageRecursiveBaseCert sig Outcome) :
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

end LanguageRecursiveBaseCert

/-- Local commutation obligation for lifting a base outcome morphism through
recursive completion. -/
structure LanguageRecursiveMorphismCert
    (source : LanguageRecursiveBaseCert sig Source)
    (target : LanguageRecursiveBaseCert sig Target)
    (transform : Source → Target) : Prop where
  oneLayer : ∀ approximation,
    FlatApproximation.mapOutcome transform
        (source.functional approximation) =
      target.functional (FlatApproximation.mapOutcome transform approximation)

theorem LanguageRecursiveMorphismCert.lift
    (cert : LanguageRecursiveMorphismCert source target transform) :
    FlatApproximation.mapOutcome transform source.semantics = target.semantics :=
  FlatApproximation.lfp_mapOutcome source.continuous target.continuous
    cert.oneLayer

/-- Local binary-relation obligations for lifting a logical relation through
recursive completion. -/
structure LanguageRecursiveRelationCert
    (left : LanguageRecursiveBaseCert sig Left)
    (right : LanguageRecursiveBaseCert sig Right)
    (relation : FlatApproximation.Carrier LanguageComp Left →
      FlatApproximation.Carrier LanguageComp Right → Prop) : Prop where
  admissible : FlatApproximation.BinaryAdmissible relation
  bottom : relation FlatApproximation.bottom FlatApproximation.bottom
  oneLayer : ∀ {leftApprox rightApprox},
    relation leftApprox rightApprox →
    relation (left.functional leftApprox) (right.functional rightApprox)

theorem LanguageRecursiveRelationCert.lift
    (cert : LanguageRecursiveRelationCert left right relation) :
    relation left.semantics right.semantics :=
  FlatApproximation.lfp_relation left.continuous right.continuous
    cert.admissible cert.bottom cert.oneLayer

end EffectSemantics
