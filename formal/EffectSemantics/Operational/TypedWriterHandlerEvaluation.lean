import EffectSemantics.Denotational.TypedShallow

namespace EffectSemantics

/-- Proof-relevant implementation witness for one typed source clause. -/
structure TypedWriterClauseModel (sig : Signature) (interface operation : Nat)
    {parameterTy responseTy : Ty}
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (clause : Comp) (clauseTyping : ∀ parameter : ClosedVal sig parameterTy,
      HasComp sig [] (clause.subst0 parameter.value) responseTy clauseEffect)
    (semantics : TypedWriterTree.AffineSemantics sig) where
  response : ClosedVal sig parameterTy →
    TypedWriterTree sig (ClosedVal sig responseTy)
  semanticFound : semantics.clause interface operation lookup = some response
  produces : ∀ parameter, ProducesTypedWriterTree sig
    (clauseTyping parameter) (response parameter)

/-- Agreement between a typed source clause table and its response-typed
Writer-tree interpretation. -/
structure ModelsTypedWriterHandler (sig : Signature) (interface : Nat)
    (source : AffineHandler) (semantics : TypedWriterTree.AffineSemantics sig)
    (clauseEffect : Effect) (sourceTyping : HasAffineHandler sig [] interface source clauseEffect) where
  present : ∀ {operation clause parameterTy responseTy}
      (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
      (found : source.lookup operation = some clause),
    TypedWriterClauseModel sig interface operation lookup clause
      (fun parameter => sourceTyping.instantiate found lookup parameter.typing)
      semantics
  absent : ∀ {operation parameterTy responseTy}
      (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩),
    source.lookup operation = none →
      semantics.clause interface operation lookup = none

/-- Type-indexed direct evaluation of one shallow handler.  Output effects are
carried by the produced tree; the source typing remains the input certificate. -/
inductive HandlesTypedWriterTree (sig : Signature) (interface : Nat)
    (handler : AffineHandler) :
    {term : Comp} → {resultTy : Ty} → {effect : Effect} →
    HasComp sig [] term resultTy effect →
    TypedWriterTree sig (ClosedVal sig resultTy) → Type where
  | returned (typing : HasComp sig [] (.ret value) resultTy effect) :
      HandlesTypedWriterTree sig interface handler typing
        (.ret ⟨value, typing.returnView.valueTyping⟩)
  | internal (step : Step term next)
      (handles : HandlesTypedWriterTree sig interface handler
        (step.preserve typing) tree) :
      HandlesTypedWriterTree sig interface handler typing tree
  | rederive {typing₁ typing₂ : HasComp sig [] term resultTy effect}
      (handles : HandlesTypedWriterTree sig interface handler typing₁ tree) :
      HandlesTypedWriterTree sig interface handler typing₂ tree
  | retarget {typing₁ : HasComp sig [] term₁ resultTy effect}
      {typing₂ : HasComp sig [] term₂ resultTy effect}
      (equal : term₁ = term₂)
      (handles : HandlesTypedWriterTree sig interface handler typing₁ tree) :
      HandlesTypedWriterTree sig interface handler typing₂ tree
  | weaken {typing : HasComp sig [] term resultTy lower}
      (handles : HandlesTypedWriterTree sig interface handler typing tree)
      (bound : lower ≤ upper) :
      HandlesTypedWriterTree sig interface handler (typing.subeffect bound) tree
  | tell {request : BaseRequest} {parameterTy : Ty}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (lookup : sig.base request.operation = some ⟨parameterTy, .unit⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      {suffix : Effect}
      (resumeTyping : HasComp sig [] (request.resume .unit) resultTy suffix)
      (bound : [EffectAtom.base 0] * suffix ≤ resultEffect)
      (handles : HandlesTypedWriterTree sig interface handler resumeTyping tail) :
      HandlesTypedWriterTree sig interface handler typing
        (.tell request.parameter tail)
  | freeOther {request : FreeRequest} {parameterTy responseTy : Ty}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (lookup : sig.free request.interface request.operation =
        some ⟨parameterTy, responseTy⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      (different : request.interface ≠ interface)
      {suffix : Effect}
      (continuation : ClosedVal sig responseTy →
        TypedWriterTree sig (ClosedVal sig resultTy))
      (resumeTyping : ∀ response : ClosedVal sig responseTy,
        HasComp sig [] (request.resume response.value) resultTy suffix)
      (bound : [EffectAtom.free request.interface] * suffix ≤ resultEffect)
      (handles : ∀ response, HandlesTypedWriterTree sig interface handler
        (resumeTyping response) (continuation response)) :
      HandlesTypedWriterTree sig interface handler typing
        (.free request.interface request.operation lookup
          ⟨request.parameter, parameterTyping⟩ continuation)
  | freeMissing {request : FreeRequest} {parameterTy responseTy : Ty}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (lookup : sig.free request.interface request.operation =
        some ⟨parameterTy, responseTy⟩)
      (parameterTyping : HasVal sig [] request.parameter parameterTy)
      (same : request.interface = interface)
      (missing : handler.lookup request.operation = none)
      {suffix : Effect}
      (continuation : ClosedVal sig responseTy →
        TypedWriterTree sig (ClosedVal sig resultTy))
      (resumeTyping : ∀ response : ClosedVal sig responseTy,
        HasComp sig [] (request.resume response.value) resultTy suffix)
      (bound : [EffectAtom.free request.interface] * suffix ≤ resultEffect)
      (handles : ∀ response, HandlesTypedWriterTree sig interface handler
        (resumeTyping response) (continuation response)) :
      HandlesTypedWriterTree sig interface handler typing
        (.free request.interface request.operation lookup
          ⟨request.parameter, parameterTyping⟩ continuation)
  | matched {request : FreeRequest}
      (typing : HasComp sig [] request.source resultTy resultEffect)
      (same : request.interface = interface)
      (found : handler.lookup request.operation = some clause)
      (answerTyping : HasComp sig [] (request.answerWith clause)
        resultTy answerEffect)
      (produces : ProducesTypedWriterTree sig answerTyping tree) :
      HandlesTypedWriterTree sig interface handler typing tree

/-- Response-typed source shallow evaluation commutes with the typed
structural tree handler. -/
noncomputable def ProducesTypedWriterTree.shallow
    {sourceTyping : HasAffineHandler sig [] interface source clauseEffect}
    (models : ModelsTypedWriterHandler sig interface source semantics
      clauseEffect sourceTyping)
    (produces : ProducesTypedWriterTree sig typing tree) :
    HandlesTypedWriterTree sig interface source typing
      (TypedWriterTree.shallow interface semantics tree) := by
  induction produces with
  | returned typing => exact .returned typing
  | internal step produces ih => exact .internal step ih
  | rederive produces ih => exact .rederive ih
  | retarget equal produces ih => exact .retarget equal ih
  | weaken produces bound ih => exact .weaken ih bound
  | tell typing selected lookup parameterTyping resumeTyping bound produces ih =>
      exact .tell typing selected lookup parameterTyping resumeTyping bound ih
  | @free resultTy resultEffect request parameterTy responseTy typing lookup
      parameterTyping suffix continuation resumeTyping requestBound produces ih =>
      by_cases same : request.interface = interface
      · subst interface
        cases found : source.lookup request.operation with
        | none =>
            rw [TypedWriterTree.shallow_forward_missing (models.absent lookup found)]
            exact .freeMissing typing lookup parameterTyping rfl found
              (fun value => TypedWriterTree.shallow request.interface semantics
                (continuation value)) resumeTyping requestBound ih
        | some clause =>
            let clauseModel := models.present lookup found
            rw [TypedWriterTree.shallow_match semantics clauseModel.semanticFound]
            let requestView := typing.exposedFreeView
            have signatureEq :
                OpDecl.mk requestView.parameterTy requestView.responseTy =
                  OpDecl.mk parameterTy responseTy :=
              Option.some.inj (requestView.lookup.symm.trans lookup)
            cases signatureEq
            let continuationTyping := requestView.openResumeTypingDefault
            have suffixBelow : suffix ≤ resultEffect :=
              Effect.le_trans (Effect.le_left_padding
                [EffectAtom.free request.interface] suffix) requestBound
            let continuationProduces := fun value =>
              ProducesTypedWriterTree.retarget
                (typing₂ := continuationTyping.subst0_preserved value.typing)
                (FreeRequest.openResume_subst0 request value.value).symm
                (ProducesTypedWriterTree.weaken (produces value) suffixBelow)
            let answerProduces := ProducesTypedWriterTree.letE
              (clauseModel.produces ⟨request.parameter, parameterTyping⟩)
              continuation continuationProduces
            exact .matched typing rfl found
              (sourceTyping.answerWithTyping typing rfl found)
              (.rederive answerProduces)
      · rw [TypedWriterTree.shallow_forward_other same]
        exact .freeOther typing lookup parameterTyping same
          (fun value => TypedWriterTree.shallow interface semantics
            (continuation value)) resumeTyping requestBound ih

end EffectSemantics
