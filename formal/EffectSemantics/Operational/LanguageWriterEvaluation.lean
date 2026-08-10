import EffectSemantics.Denotational.LanguageWriterTree

namespace EffectSemantics

open EffectLanguage

structure LanguageFreePrincipal
    {request : LanguageFreeRequest}
    (typing : HasLanguageComp sig [] request.source resultTy resultEffect) where
  responseTy : LanguageTy
  suffix : EffectLanguage
  bound : EffectLanguage.seq (principal [EffectAtom.free request.interface])
    suffix ≤ resultEffect
  resumeTyping : ∀ response : LanguageClosedVal sig responseTy,
    HasLanguageComp sig [] (request.resume response.value) resultTy suffix
  lookup : ∃ parameterTy,
    sig.free request.interface request.operation = some ⟨parameterTy, responseTy⟩

noncomputable def TypedLanguageFreeRequest.principal
    {request : LanguageFreeRequest}
    {typing : HasLanguageComp sig [] request.source resultTy resultEffect}
    (requestTyping : TypedLanguageFreeRequest typing) :
    LanguageFreePrincipal typing := by
  let factor := requestTyping.contextTyping.principalFactor
    (newHole := EffectLanguage.principal 1) requestTyping.requestBelowHole
  refine ⟨requestTyping.responseTy, factor.suffix, factor.bound, ?_,
    ⟨requestTyping.parameterTy, requestTyping.lookup⟩⟩
  intro response
  have resumed := factor.typing.plugTyping (HasLanguageComp.ret response.typing)
  rw [EffectLanguage.seq_one_left] at resumed
  exact resumed

structure LanguageBasePrincipal
    {request : LanguageBaseRequest}
    (typing : HasLanguageComp sig [] request.source resultTy resultEffect) where
  responseTy : LanguageTy
  suffix : EffectLanguage
  bound : EffectLanguage.seq (principal [EffectAtom.base request.operation])
    suffix ≤ resultEffect
  resumeTyping : ∀ response : LanguageClosedVal sig responseTy,
    HasLanguageComp sig [] (request.resume response.value) resultTy suffix
  lookup : ∃ parameterTy,
    sig.base request.operation = some ⟨parameterTy, responseTy⟩

noncomputable def TypedLanguageBaseRequest.principal
    {request : LanguageBaseRequest}
    {typing : HasLanguageComp sig [] request.source resultTy resultEffect}
    (requestTyping : TypedLanguageBaseRequest typing) :
    LanguageBasePrincipal typing := by
  let factor := requestTyping.contextTyping.principalFactor
    (newHole := EffectLanguage.principal 1) requestTyping.requestBelowHole
  refine ⟨requestTyping.responseTy, factor.suffix, factor.bound, ?_,
    ⟨requestTyping.parameterTy, requestTyping.lookup⟩⟩
  intro response
  have resumed := factor.typing.plugTyping (HasLanguageComp.ret response.typing)
  rw [EffectLanguage.seq_one_left] at resumed
  exact resumed

/-- A closed typed source computation unfolds to a response-typed
Writer/free tree.  The relation is partial in the presence of recursion. -/
inductive ProducesLanguageWriterTree (sig : LanguageSignature) :
    {term : FinLanguageComp} → {resultTy : LanguageTy} →
    {effect : EffectLanguage} →
    (typing : HasLanguageComp sig [] term resultTy effect) →
    LanguageWriterTree sig (LanguageClosedVal sig resultTy) → Type where
  | returned (typing : HasLanguageComp sig [] (.ret value) resultTy effect) :
      ProducesLanguageWriterTree sig typing
        (.ret ⟨value, typing.returnView.valueTyping⟩)
  | internal (step : term ⟶ next)
      (produces : ProducesLanguageWriterTree sig (step.preserve typing) tree) :
      ProducesLanguageWriterTree sig typing tree
  | rederive {typing₁ typing₂ : HasLanguageComp sig [] term resultTy effect}
      (produces : ProducesLanguageWriterTree sig typing₁ tree) :
      ProducesLanguageWriterTree sig typing₂ tree
  | retarget
      {typing₁ : HasLanguageComp sig [] term₁ resultTy effect}
      {typing₂ : HasLanguageComp sig [] term₂ resultTy effect}
      (equal : term₁ = term₂)
      (produces : ProducesLanguageWriterTree sig typing₁ tree) :
      ProducesLanguageWriterTree sig typing₂ tree
  | weaken {typing : HasLanguageComp sig [] term resultTy lower}
      (produces : ProducesLanguageWriterTree sig typing tree)
      (bound : lower ≤ upper) :
      ProducesLanguageWriterTree sig (typing.subeffect bound) tree
  | tell {request : LanguageBaseRequest} {parameterTy : LanguageTy}
      (typing : HasLanguageComp sig [] request.source resultTy resultEffect)
      (selected : request.operation = 0)
      (lookup : sig.base request.operation = some ⟨parameterTy, .unit⟩)
      (parameterTyping : HasLanguageVal sig [] request.parameter parameterTy)
      {suffix : EffectLanguage}
      (resumeTyping : HasLanguageComp sig [] (request.resume .unit) resultTy suffix)
      (bound : EffectLanguage.seq (principal [EffectAtom.base 0]) suffix ≤
        resultEffect)
      (produces : ProducesLanguageWriterTree sig resumeTyping tail) :
      ProducesLanguageWriterTree sig typing (.tell request.parameter tail)
  | free {request : LanguageFreeRequest} {parameterTy responseTy : LanguageTy}
      (typing : HasLanguageComp sig [] request.source resultTy resultEffect)
      (lookup : sig.free request.interface request.operation =
        some ⟨parameterTy, responseTy⟩)
      (parameterTyping : HasLanguageVal sig [] request.parameter parameterTy)
      {suffix : EffectLanguage}
      (continuation : LanguageClosedVal sig responseTy →
        LanguageWriterTree sig (LanguageClosedVal sig resultTy))
      (resumeTyping : ∀ response : LanguageClosedVal sig responseTy,
        HasLanguageComp sig [] (request.resume response.value) resultTy suffix)
      (bound : EffectLanguage.seq
        (principal [EffectAtom.free request.interface]) suffix ≤ resultEffect)
      (produces : ∀ response,
        ProducesLanguageWriterTree sig (resumeTyping response)
          (continuation response)) :
      ProducesLanguageWriterTree sig typing
        (.free request.interface request.operation lookup
          ⟨request.parameter, parameterTyping⟩ continuation)

/-- Relational denotational soundness of one internal source step.  The tree
semantics is intentionally a relation (it remains partial once `fixLam` is
available), so this is the precise counterpart of an equality of total
denotations. -/
noncomputable def ProducesLanguageWriterTree.internalStepInvariant
    {typing : HasLanguageComp sig [] term resultTy effect}
    (step : term ⟶ next)
    {tree : LanguageWriterTree sig (LanguageClosedVal sig resultTy)}
    (produces : ProducesLanguageWriterTree sig (step.preserve typing) tree) :
    ProducesLanguageWriterTree sig typing tree :=
  .internal step produces

/-- CBV source sequencing is semantic tree bind. -/
noncomputable def ProducesLanguageWriterTree.letE
    {boundTyping : HasLanguageComp sig [] bound boundTy boundEffect}
    {bodyTyping : HasLanguageComp sig (boundTy :: []) body resultTy bodyEffect}
    (boundProduces : ProducesLanguageWriterTree sig boundTyping tree)
    (continuation : LanguageClosedVal sig boundTy →
      LanguageWriterTree sig (LanguageClosedVal sig resultTy))
    (bodyProduces : ∀ value,
      ProducesLanguageWriterTree sig
        (bodyTyping.subst0_preserved value.typing) (continuation value)) :
    ProducesLanguageWriterTree sig (.letE boundTyping bodyTyping)
      (tree.bind continuation) := by
  induction boundProduces generalizing body bodyEffect with
  | returned typing =>
      apply ProducesLanguageWriterTree.internal .letReturn
      let value : LanguageClosedVal sig _ :=
        ⟨_, typing.returnView.valueTyping⟩
      exact ProducesLanguageWriterTree.rederive
        (typing₂ := LanguageStep.letReturn.preserve (typing.letE bodyTyping))
        (.weaken (bodyProduces value)
          (EffectLanguage.le_seq_of_pure_left typing.returnView.pureBelow))
  | internal step produces ih =>
      apply ProducesLanguageWriterTree.internal (.underLet step)
      exact .rederive (ih continuation bodyProduces)
  | rederive produces ih => exact .rederive (ih continuation bodyProduces)
  | retarget equal produces ih =>
      exact .retarget (congrArg (fun term => LanguageComp.letE term body) equal)
        (ih continuation bodyProduces)
  | weaken produces bound ih =>
      exact .rederive (.weaken (ih continuation bodyProduces)
        (EffectLanguage.seq_mono bound (EffectLanguage.le_refl bodyEffect)))
  | @tell sourceResultTy resultEffect tail request parameterTy typing selected
      lookup parameterTyping suffix resumeTyping requestBound produces ih =>
      let outerTyping := HasLanguageComp.letE typing bodyTyping
      let resumedTyping := HasLanguageComp.letE resumeTyping bodyTyping
      let outerRequest := request.outerLet body
      let underLetTyping : HasLanguageComp sig [] outerRequest.source resultTy
          (EffectLanguage.seq resultEffect bodyEffect) := by
        simpa [outerRequest] using outerTyping
      let underLetResumeTyping : HasLanguageComp sig []
          (outerRequest.resume .unit) resultTy
          (EffectLanguage.seq suffix bodyEffect) := by
        simpa [outerRequest] using resumedTyping
      have combinedBound : EffectLanguage.seq (principal [EffectAtom.base 0])
          (EffectLanguage.seq suffix bodyEffect) ≤
          EffectLanguage.seq resultEffect bodyEffect := by
        rw [← EffectLanguage.seq_assoc]
        exact EffectLanguage.seq_mono requestBound
          (EffectLanguage.le_refl bodyEffect)
      change ProducesLanguageWriterTree sig (typing.letE bodyTyping)
        (.tell request.parameter (tail.bind continuation))
      apply ProducesLanguageWriterTree.retarget
        (typing₂ := typing.letE bodyTyping)
        (LanguageBaseRequest.outerLet_source request body)
      exact ProducesLanguageWriterTree.tell
        (request := outerRequest) (typing := underLetTyping)
        selected lookup parameterTyping
        (resumeTyping := underLetResumeTyping) combinedBound
        (ProducesLanguageWriterTree.retarget
          (typing₂ := underLetResumeTyping)
          (LanguageBaseRequest.outerLet_resume request body .unit).symm
          (ih continuation bodyProduces))
  | @free sourceResultTy resultEffect request parameterTy responseTy typing lookup
      parameterTyping suffix requestContinuation resumeTyping requestBound produces ih =>
      let outerTyping := HasLanguageComp.letE typing bodyTyping
      let outerRequest := request.outerLet body
      let underLetTyping : HasLanguageComp sig [] outerRequest.source resultTy
          (EffectLanguage.seq resultEffect bodyEffect) := by
        simpa [outerRequest] using outerTyping
      let underLetResumeTyping := fun response : LanguageClosedVal sig responseTy =>
        (show HasLanguageComp sig [] (outerRequest.resume response.value)
            resultTy (EffectLanguage.seq suffix bodyEffect) by
          simpa [outerRequest] using
            (HasLanguageComp.letE (resumeTyping response) bodyTyping))
      have combinedBound : EffectLanguage.seq
          (principal [EffectAtom.free request.interface])
          (EffectLanguage.seq suffix bodyEffect) ≤
          EffectLanguage.seq resultEffect bodyEffect := by
        rw [← EffectLanguage.seq_assoc]
        exact EffectLanguage.seq_mono requestBound
          (EffectLanguage.le_refl bodyEffect)
      change ProducesLanguageWriterTree sig (typing.letE bodyTyping)
        (.free request.interface request.operation lookup
          ⟨request.parameter, parameterTyping⟩
          (fun response => (requestContinuation response).bind continuation))
      apply ProducesLanguageWriterTree.retarget
        (typing₂ := typing.letE bodyTyping)
        (LanguageFreeRequest.outerLet_source request body)
      exact ProducesLanguageWriterTree.free
        (request := outerRequest) (typing := underLetTyping)
        lookup parameterTyping
        (continuation := fun response =>
          (requestContinuation response).bind continuation)
        (resumeTyping := underLetResumeTyping) combinedBound
        (fun response => ProducesLanguageWriterTree.retarget
          (typing₂ := underLetResumeTyping response)
          (LanguageFreeRequest.outerLet_resume request body response.value).symm
          (ih response continuation bodyProduces))

noncomputable def ProducesLanguageWriterTree.effectSound
    {sig : LanguageSignature} {term : FinLanguageComp}
    {resultTy : LanguageTy} {effect : EffectLanguage}
    {typing : HasLanguageComp sig [] term resultTy effect}
    {tree : LanguageWriterTree sig (LanguageClosedVal sig resultTy)}
    (produces : ProducesLanguageWriterTree sig typing tree) :
    LanguageWriterTree.HasEffect tree effect := by
  induction produces with
  | returned typing =>
      exact LanguageWriterTree.HasEffect.ret.weaken typing.returnView.pureBelow
  | internal step produces ih => exact ih
  | rederive produces ih => exact ih
  | retarget equal produces ih => exact ih
  | weaken produces bound ih => exact ih.weaken bound
  | tell typing selected lookup parameterTyping resumeTyping bound produces ih =>
      exact (LanguageWriterTree.HasEffect.tell ih).weaken bound
  | free typing lookup parameterTyping continuation resumeTyping bound produces ih =>
      exact (LanguageWriterTree.HasEffect.free ih).weaken bound

/-- A source/tree evaluation can only produce observations admitted by the
declared ordered effect upper bound.  This is the executable tree-level form
of the Chapter-I may-effect theorem. -/
noncomputable def ProducesLanguageWriterTree.observationEffectSound
    {typing : HasLanguageComp sig [] term resultTy effect}
    {tree : LanguageWriterTree sig (LanguageClosedVal sig resultTy)}
    (produces : ProducesLanguageWriterTree sig typing tree)
    (_observes : LanguageWriterTree.Observes tree log value) :
    LanguageWriterTree.HasEffect tree effect :=
  produces.effectSound

end EffectSemantics
