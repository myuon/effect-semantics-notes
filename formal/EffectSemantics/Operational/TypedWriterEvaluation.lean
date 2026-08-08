import EffectSemantics.Denotational.TypedWriterTree
import EffectSemantics.Operational.WriterHandlerEvaluation

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
  | retarget {typing₁ : HasComp sig [] term₁ resultTy effect}
      {typing₂ : HasComp sig [] term₂ resultTy effect}
      (equal : term₁ = term₂)
      (produces : ProducesTypedWriterTree sig typing₁ tree) :
      ProducesTypedWriterTree sig typing₂ tree
  | weaken {typing : HasComp sig [] term resultTy lower}
      (produces : ProducesTypedWriterTree sig typing tree)
      (bound : lower ≤ upper) :
      ProducesTypedWriterTree sig (typing.subeffect bound) tree
  | tell {request : BaseRequest}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      {parameterTy : Ty} (lookup : sig.base request.operation =
        some ⟨parameterTy, .unit⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      {suffix : Effect}
      (resumeTyping : HasComp sig [] (request.resume .unit) resultTy suffix)
      (bound : [EffectAtom.base 0] * suffix ≤ resultEffect)
      (produces : ProducesTypedWriterTree sig resumeTyping tail) :
      ProducesTypedWriterTree sig typing (.tell request.parameter tail)
  | free {request : FreeRequest} {parameterTy responseTy : Ty}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (lookup : sig.free request.interface request.operation =
        some ⟨parameterTy, responseTy⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      {suffix : Effect}
      (continuation : ClosedVal sig responseTy →
        TypedWriterTree sig (ClosedVal sig resultTy))
      (resumeTyping : ∀ response : ClosedVal sig responseTy,
        HasComp sig [] (request.resume response.value) resultTy suffix)
      (bound : [EffectAtom.free request.interface] * suffix ≤ resultEffect)
      (produces : ∀ response,
        ProducesTypedWriterTree sig (resumeTyping response)
          (continuation response)) :
      ProducesTypedWriterTree sig typing
        (.free request.interface request.operation
          lookup ⟨request.parameter, parameterTyping⟩
          continuation)

/-- Type-indexed CBV sequencing is bind of response-typed behavior trees. -/
noncomputable def ProducesTypedWriterTree.letE
    {boundTyping : HasComp sig [] bound boundTy boundEffect}
    {bodyTyping : HasComp sig (boundTy :: []) body resultTy bodyEffect}
    (boundProduces : ProducesTypedWriterTree sig boundTyping tree)
    (continuation : ClosedVal sig boundTy →
      TypedWriterTree sig (ClosedVal sig resultTy))
    (bodyProduces : ∀ value,
      ProducesTypedWriterTree sig
        (bodyTyping.subst0_preserved value.typing) (continuation value)) :
    ProducesTypedWriterTree sig (.letE boundTyping bodyTyping)
      (tree.bind continuation) := by
  induction boundProduces generalizing body bodyEffect with
  | returned typing =>
      apply ProducesTypedWriterTree.internal .letReturn
      let value : ClosedVal sig _ := ⟨_, typing.returnView.valueTyping⟩
      change ProducesTypedWriterTree sig
        (Step.letReturn.preserve (typing.letE bodyTyping))
        (continuation value)
      exact ProducesTypedWriterTree.rederive
        (typing₁ := (bodyTyping.subst0_preserved value.typing).subeffect
          (Effect.le_left_padding _ _))
        (typing₂ := Step.letReturn.preserve (typing.letE bodyTyping))
        (.weaken (bodyProduces value) (Effect.le_left_padding _ _))
  | internal step produces ih =>
      apply ProducesTypedWriterTree.internal (.underLet step)
      exact .rederive (ih continuation bodyProduces)
  | rederive produces ih =>
      exact .rederive (ih continuation bodyProduces)
  | retarget equal produces ih =>
      exact .retarget (congrArg (fun term => Comp.letE term body) equal)
        (ih continuation bodyProduces)
  | weaken produces bound ih =>
      exact .rederive (.weaken (ih continuation bodyProduces)
        (Effect.le_seq bound (Effect.le_refl bodyEffect)))
  | @tell sourceResultTy resultEffect tail request typing selected parameterTy
      lookup parameterTyping suffix resumeTyping requestBound produces ih =>
      let outerTyping := HasComp.letE typing bodyTyping
      let resumedTyping := HasComp.letE resumeTyping bodyTyping
      let underLetTyping : HasComp sig [] (request.underLet body).source resultTy
          (resultEffect * bodyEffect) := by simpa using outerTyping
      let underLetResumeTyping : HasComp sig []
          ((request.underLet body).resume .unit) resultTy
          (suffix * bodyEffect) := by simpa using resumedTyping
      have combinedBound : [EffectAtom.base 0] * (suffix * bodyEffect) ≤
          resultEffect * bodyEffect := by
        rw [← Effect.mul_assoc]
        exact Effect.le_seq requestBound (Effect.le_refl bodyEffect)
      change ProducesTypedWriterTree sig (typing.letE bodyTyping)
        (.tell request.parameter (tail.bind continuation))
      apply ProducesTypedWriterTree.retarget
        (typing₂ := typing.letE bodyTyping)
        (BaseRequest.underLet_source request body)
      simpa [BaseRequest.underLet] using
        (ProducesTypedWriterTree.tell
          (request := request.underLet body)
          (typing := underLetTyping)
          selected lookup parameterTyping
          (resumeTyping := underLetResumeTyping)
          combinedBound
          (ProducesTypedWriterTree.retarget
            (typing₂ := underLetResumeTyping)
            (BaseRequest.underLet_resume request body .unit).symm
            (ih continuation bodyProduces)))
  | @free sourceResultTy resultEffect request parameterTy responseTy typing lookup
      parameterTyping suffix requestContinuation resumeTyping requestBound produces ih =>
      let outerTyping := HasComp.letE typing bodyTyping
      let resumedTyping := fun response => HasComp.letE (resumeTyping response) bodyTyping
      let underLetTyping : HasComp sig [] (request.underLet body).source resultTy
          (resultEffect * bodyEffect) := by simpa using outerTyping
      let underLetResumeTyping := fun response : ClosedVal sig responseTy =>
        (show HasComp sig [] ((request.underLet body).resume response.value)
            resultTy (suffix * bodyEffect) by
          simpa using resumedTyping response)
      have combinedBound :
          [EffectAtom.free request.interface] * (suffix * bodyEffect) ≤
            resultEffect * bodyEffect := by
        rw [← Effect.mul_assoc]
        exact Effect.le_seq requestBound (Effect.le_refl bodyEffect)
      change ProducesTypedWriterTree sig (typing.letE bodyTyping)
        (.free request.interface request.operation lookup
          ⟨request.parameter, parameterTyping⟩
          (fun response => (requestContinuation response).bind continuation))
      apply ProducesTypedWriterTree.retarget
        (typing₂ := typing.letE bodyTyping)
        (FreeRequest.underLet_source request body)
      simpa [FreeRequest.underLet] using
        (ProducesTypedWriterTree.free
          (request := request.underLet body)
          (typing := underLetTyping)
          lookup parameterTyping
          (continuation := fun response =>
            (requestContinuation response).bind continuation)
          (resumeTyping := underLetResumeTyping)
          combinedBound
          (fun response => ProducesTypedWriterTree.retarget
            (typing₂ := underLetResumeTyping response)
            (FreeRequest.underLet_resume request body response.value).symm
            (ih response continuation bodyProduces)))

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
  | retarget equal produces ih => exact ih
  | weaken produces bound ih => exact ih.weaken bound
  | tell typing selected lookup parameterTyping resumeTyping bound produces ih =>
      exact (TypedWriterTree.HasEffect.tell ih).weaken bound
  | free typing lookup parameterTyping continuation resumeTyping bound produces ih =>
      exact (TypedWriterTree.HasEffect.free ih).weaken bound

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
  | retarget {typing₁ : HasComp sig [] term₁ resultTy effect}
      {typing₂ : HasComp sig [] term₂ resultTy effect}
      (equal : term₁ = term₂) (runs : TypedWriterRuns sig typing₁ log value) :
      TypedWriterRuns sig typing₂ log value
  | weaken {typing : HasComp sig [] term resultTy lower}
      (runs : TypedWriterRuns sig typing log value) (bound : lower ≤ upper) :
      TypedWriterRuns sig (typing.subeffect bound) log value
  | tell {request : BaseRequest} {parameterTy : Ty}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (lookup : sig.base request.operation = some ⟨parameterTy, .unit⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      {suffix : Effect}
      (resumeTyping : HasComp sig [] (request.resume .unit) resultTy suffix)
      (bound : [EffectAtom.base 0] * suffix ≤ resultEffect)
      (runs : TypedWriterRuns sig resumeTyping log value) :
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
  | retarget equal produces ih => exact .retarget equal (ih observes)
  | weaken produces bound ih => exact .weaken (ih observes) bound
  | tell typing selected lookup parameterTyping resumeTyping bound produces ih =>
      cases observes with
      | tell tailObserved =>
          exact .tell typing selected lookup parameterTyping resumeTyping bound
            (ih tailObserved)
  | free typing lookup parameterTyping continuation resumeTyping bound produces ih =>
      cases observes

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
  | retarget equal runs ih =>
      exact ⟨ih.1, .retarget equal ih.2.1, ih.2.2⟩
  | weaken runs bound ih =>
      exact ⟨ih.1, .weaken ih.2.1 bound, ih.2.2⟩
  | tell typing selected lookup parameterTyping resumeTyping bound runs ih =>
      exact ⟨.tell _ ih.1,
        .tell typing selected lookup parameterTyping resumeTyping bound ih.2.1,
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
