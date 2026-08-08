import EffectSemantics.Denotational.TypedWriterTree

namespace EffectSemantics

def ClosedVal.unitOfEq {sig : Signature} {ty : Ty} (equal : ty = .unit) :
    ClosedVal sig ty := by
  subst ty
  exact ⟨.unit, .unit⟩

structure FreePrincipal (sig : Signature) (request : FreeRequest)
    (resultTy : Ty) (resultEffect : Effect)
    (typing : TypedFreeRequest sig [] request resultTy resultEffect) where
  suffix : Effect
  bound : [EffectAtom.free request.interface] * suffix ≤ resultEffect
  resumeTyping : ∀ response : ClosedVal sig typing.responseTy,
    HasComp sig [] (request.resume response.value) resultTy suffix

noncomputable def TypedFreeRequest.principal
    (typing : TypedFreeRequest sig [] request resultTy resultEffect) :
    FreePrincipal sig request resultTy resultEffect typing := by
  let factor := typing.contextTyping.principalFactor
    (newHole := (1 : Effect)) typing.requestBelowHole
  refine ⟨factor.suffix, factor.bound, ?_⟩
  intro response
  change HasComp sig [] (request.context.plug (.ret response.value))
    resultTy factor.suffix
  simpa using factor.typing.plugTyping (HasComp.ret response.typing)

structure BasePrincipal (sig : Signature) (request : BaseRequest)
    (resultTy : Ty) (resultEffect : Effect)
    (typing : TypedBaseRequest sig [] request resultTy resultEffect) where
  suffix : Effect
  bound : [EffectAtom.base request.operation] * suffix ≤ resultEffect
  resumeTyping : ∀ response : ClosedVal sig typing.responseTy,
    HasComp sig [] (request.resume response.value) resultTy suffix

noncomputable def TypedBaseRequest.principal
    (typing : TypedBaseRequest sig [] request resultTy resultEffect) :
    BasePrincipal sig request resultTy resultEffect typing := by
  let factor := typing.contextTyping.principalFactor
    (newHole := (1 : Effect)) typing.requestBelowHole
  refine ⟨factor.suffix, factor.bound, ?_⟩
  intro response
  change HasComp sig [] (request.context.plug (.ret response.value))
    resultTy factor.suffix
  simpa using factor.typing.plugTyping (HasComp.ret response.typing)

/-- A typed source computation produces a response-typed tree.  The typing
derivation itself is the index, so internal stepping and request resumptions
cannot silently change the declared result type. -/
inductive ProducesTypedWriterTree (sig : Signature) :
    {term : Comp} → {resultTy : Ty} → {effect : Effect} →
    (typing : HasComp sig [] term resultTy effect) →
    TypedWriterTree sig (ClosedVal sig resultTy) → Type where
  | returned (typing : HasComp sig [] (.ret value) resultTy effect) :
      ProducesTypedWriterTree sig typing
        (.ret ⟨value, typing.returnView.valueTyping⟩)
  | internal (step : Step term next)
      (produces : ProducesTypedWriterTree sig (step.preserve typing) tree) :
      ProducesTypedWriterTree sig typing tree
  | rederive {typing₁ typing₂ : HasComp sig [] term resultTy effect}
      (produces : ProducesTypedWriterTree sig typing₁ tree) :
      ProducesTypedWriterTree sig typing₂ tree
  | weaken {typing : HasComp sig [] term resultTy lower}
      (produces : ProducesTypedWriterTree sig typing tree)
      (bound : lower ≤ upper) :
      ProducesTypedWriterTree sig (typing.subeffect bound) tree
  | tell {request : BaseRequest}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (unitResponse : typing.exposedBaseView.responseTy = .unit)
      (produces : ProducesTypedWriterTree sig
        (typing.exposedBaseView.principal.resumeTyping
          (ClosedVal.unitOfEq unitResponse)) tail) :
      ProducesTypedWriterTree sig typing (.tell request.parameter tail)
  | free {request : FreeRequest}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (continuation : ClosedVal sig typing.exposedFreeView.responseTy →
        TypedWriterTree sig (ClosedVal sig resultTy))
      (produces : ∀ response,
        ProducesTypedWriterTree sig
          (typing.exposedFreeView.principal.resumeTyping response)
          (continuation response)) :
      ProducesTypedWriterTree sig typing
        (.free request.interface request.operation
          typing.exposedFreeView.lookup
          ⟨request.parameter, typing.exposedFreeView.parameterTyping⟩
          continuation)

/-- The produced typed tree carries a grade below the source typing bound. -/
noncomputable def ProducesTypedWriterTree.effectSound
    {sig : Signature} {term : Comp} {resultTy : Ty} {effect : Effect}
    {typing : HasComp sig [] term resultTy effect}
    {tree : TypedWriterTree sig (ClosedVal sig resultTy)}
    (produces : ProducesTypedWriterTree sig typing tree) :
    TypedWriterTree.HasEffect tree effect := by
  induction produces with
  | returned typing =>
      exact TypedWriterTree.HasEffect.ret.weaken typing.returnView.pureBelow
  | internal step produces ih => exact ih
  | rederive produces ih => exact ih
  | weaken produces bound ih => exact ih.weaken bound
  | tell typing selected unitResponse produces ih =>
      let principal := typing.exposedBaseView.principal
      have bound := principal.bound
      rw [selected] at bound
      exact (TypedWriterTree.HasEffect.tell ih).weaken bound
  | free typing continuation produces ih =>
      let principal := typing.exposedFreeView.principal
      exact (TypedWriterTree.HasEffect.free ih).weaken principal.bound

inductive TypedWriterRuns (sig : Signature) :
    {term : Comp} → {resultTy : Ty} → {effect : Effect} →
    (typing : HasComp sig [] term resultTy effect) →
    List Val → ClosedVal sig resultTy → Type where
  | returned (typing : HasComp sig [] (.ret value) resultTy effect) :
      TypedWriterRuns sig typing [] ⟨value, typing.returnView.valueTyping⟩
  | internal (step : Step term next)
      (runs : TypedWriterRuns sig (step.preserve typing) log value) :
      TypedWriterRuns sig typing log value
  | rederive {typing₁ typing₂ : HasComp sig [] term resultTy effect}
      (runs : TypedWriterRuns sig typing₁ log value) :
      TypedWriterRuns sig typing₂ log value
  | weaken {typing : HasComp sig [] term resultTy lower}
      (runs : TypedWriterRuns sig typing log value) (bound : lower ≤ upper) :
      TypedWriterRuns sig (typing.subeffect bound) log value
  | tell {request : BaseRequest}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (unitResponse : typing.exposedBaseView.responseTy = .unit)
      (runs : TypedWriterRuns sig
        (typing.exposedBaseView.principal.resumeTyping
          (ClosedVal.unitOfEq unitResponse)) log value) :
      TypedWriterRuns sig typing (request.parameter :: log) value

noncomputable def ProducesTypedWriterTree.sound
    (produces : ProducesTypedWriterTree sig typing tree)
    (observes : TypedWriterTree.Observes tree log value) :
    TypedWriterRuns sig typing log value := by
  induction produces generalizing log with
  | returned typing =>
      cases observes
      exact .returned typing
  | internal step produces ih =>
      exact .internal step (ih observes)
  | rederive produces ih => exact .rederive (ih observes)
  | weaken produces bound ih => exact .weaken (ih observes) bound
  | tell typing selected unitResponse produces ih =>
      cases observes with
      | tell tailObserved =>
          exact .tell typing selected unitResponse (ih tailObserved)
  | free typing continuation produces ih => cases observes

noncomputable def TypedWriterRuns.complete
    (runs : TypedWriterRuns sig typing log value) :
    Σ tree, ProducesTypedWriterTree sig typing tree ×
      TypedWriterTree.Observes tree log value := by
  induction runs with
  | returned typing =>
      exact ⟨.ret ⟨_, typing.returnView.valueTyping⟩, .returned typing, .ret⟩
  | internal step runs ih =>
      exact ⟨ih.1, .internal step ih.2.1, ih.2.2⟩
  | rederive runs ih =>
      exact ⟨ih.1, .rederive ih.2.1, ih.2.2⟩
  | weaken runs bound ih =>
      exact ⟨ih.1, .weaken ih.2.1 bound, ih.2.2⟩
  | tell typing selected unitResponse runs ih =>
      exact ⟨.tell _ ih.1,
        .tell typing selected unitResponse ih.2.1,
        .tell ih.2.2⟩

/-- Typed finite Writer adequacy, with both source typing and response typing
retained in the witness. -/
theorem typed_writer_operational_tree_adequacy :
    Nonempty (TypedWriterRuns sig typing log value) ↔
      Nonempty (Σ tree, ProducesTypedWriterTree sig typing tree ×
        TypedWriterTree.Observes tree log value) := by
  constructor
  · rintro ⟨runs⟩
    exact ⟨runs.complete⟩
  · rintro ⟨tree, produces, observes⟩
    exact ⟨produces.sound observes⟩

end EffectSemantics
