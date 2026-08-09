import EffectSemantics.Metatheory.LanguageProgress

namespace EffectSemantics

open EffectLanguage

inductive LanguageFrame where
  | letE (body : FinLanguageComp)

abbrev LanguageEvalContext := List LanguageFrame

def LanguageFrame.plug : LanguageFrame → FinLanguageComp → FinLanguageComp
  | .letE body, bound => .letE bound body

def LanguageEvalContext.plug : LanguageEvalContext → FinLanguageComp → FinLanguageComp
  | [], term => term
  | frame :: rest, term =>
      LanguageEvalContext.plug rest (frame.plug term)

theorem LanguageEvalContext.plug_append
    (left right : LanguageEvalContext) (term : FinLanguageComp) :
    LanguageEvalContext.plug (left ++ right) term =
      LanguageEvalContext.plug right (LanguageEvalContext.plug left term) := by
  induction left generalizing term with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.cons_append, LanguageEvalContext.plug]
      exact ih (frame.plug term)

def LanguageFrame.rename (rename : Nat → Nat) : LanguageFrame → LanguageFrame
  | .letE body => .letE (body.rename (liftLanguageRen rename))

def LanguageEvalContext.rename (rename : Nat → Nat)
    (context : LanguageEvalContext) : LanguageEvalContext :=
  context.map (LanguageFrame.rename rename)

theorem LanguageEvalContext.plug_subst_rename_cancel
    (context : LanguageEvalContext) (rename : Nat → Nat)
    (subst : Nat → FinLanguageVal)
    (cancel : ∀ index, subst (rename index) = .var index)
    {transformed original : FinLanguageComp}
    (hole : transformed.subst subst = original) :
    (LanguageEvalContext.plug (LanguageEvalContext.rename rename context)
      transformed).subst subst = LanguageEvalContext.plug context original := by
  induction context generalizing transformed original with
  | nil => exact hole
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          apply ih
          simp only [LanguageFrame.rename,
            LanguageFrame.plug, LanguageComp.subst]
          congr
          exact LanguageComp.subst_rename_cancel
            (liftLanguageRen rename) (liftLanguageSubst subst)
            (fun index => by
              cases index <;>
                simp [liftLanguageRen, liftLanguageSubst,
                  LanguageVal.rename, cancel]) body

structure LanguageFreeRequest where
  interface : Nat
  operation : Nat
  parameter : FinLanguageVal
  context : LanguageEvalContext

def LanguageFreeRequest.source (request : LanguageFreeRequest) : FinLanguageComp :=
  LanguageEvalContext.plug request.context
    (.freeOp request.interface request.operation request.parameter)

def LanguageFreeRequest.openResume (request : LanguageFreeRequest) :
    FinLanguageComp :=
  LanguageEvalContext.plug
    (LanguageEvalContext.rename (· + 1) request.context) (.ret (.var 0))

def LanguageFreeRequest.resume (request : LanguageFreeRequest)
    (response : FinLanguageVal) : FinLanguageComp :=
  LanguageEvalContext.plug request.context (.ret response)

@[simp] theorem LanguageFreeRequest.openResume_subst0
    (request : LanguageFreeRequest) (response : FinLanguageVal) :
    request.openResume.subst0 response = request.resume response := by
  apply LanguageEvalContext.plug_subst_rename_cancel request.context (· + 1)
    (fun | 0 => response | index + 1 => .var index)
  · intro index
    rfl
  · rfl

def LanguageFreeRequest.outerLet (request : LanguageFreeRequest)
    (body : FinLanguageComp) : LanguageFreeRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem LanguageFreeRequest.outerLet_source
    (request : LanguageFreeRequest) (body : FinLanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold LanguageFreeRequest.outerLet LanguageFreeRequest.source
  rw [LanguageEvalContext.plug_append]
  rfl

@[simp] theorem LanguageFreeRequest.outerLet_resume
    (request : LanguageFreeRequest) (body : FinLanguageComp)
    (response : FinLanguageVal) :
    (request.outerLet body).resume response =
      .letE (request.resume response) body := by
  unfold LanguageFreeRequest.outerLet LanguageFreeRequest.resume
  rw [LanguageEvalContext.plug_append]
  rfl

structure LanguageBaseRequest where
  operation : Nat
  parameter : FinLanguageVal
  context : LanguageEvalContext

def LanguageBaseRequest.source (request : LanguageBaseRequest) : FinLanguageComp :=
  LanguageEvalContext.plug request.context
    (.baseOp request.operation request.parameter)

def LanguageBaseRequest.resume (request : LanguageBaseRequest)
    (response : FinLanguageVal) : FinLanguageComp :=
  LanguageEvalContext.plug request.context (.ret response)

def LanguageBaseRequest.outerLet (request : LanguageBaseRequest)
    (body : FinLanguageComp) : LanguageBaseRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem LanguageBaseRequest.outerLet_source
    (request : LanguageBaseRequest) (body : FinLanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold LanguageBaseRequest.outerLet LanguageBaseRequest.source
  rw [LanguageEvalContext.plug_append]
  rfl

@[simp] theorem LanguageBaseRequest.outerLet_resume
    (request : LanguageBaseRequest) (body : FinLanguageComp)
    (response : FinLanguageVal) :
    (request.outerLet body).resume response =
      .letE (request.resume response) body := by
  unfold LanguageBaseRequest.outerLet LanguageBaseRequest.resume
  rw [LanguageEvalContext.plug_append]
  rfl

inductive LanguageBoundaryView : FinLanguageComp → Type where
  | base (request : LanguageBaseRequest) : LanguageBoundaryView request.source
  | free (request : LanguageFreeRequest) : LanguageBoundaryView request.source

def LanguageBoundary.view : LanguageBoundary term → LanguageBoundaryView term
  | .base => .base ⟨_, _, []⟩
  | .free => .free ⟨_, _, _, []⟩
  | .underLet inner =>
      match inner.view with
      | .base request => by simpa using LanguageBoundaryView.base (request.outerLet _)
      | .free request => by simpa using LanguageBoundaryView.free (request.outerLet _)

structure LanguageLetView
    (typing : HasLanguageComp sig ctx (.letE bound body) resultTy effect) where
  boundTy : LanguageTy
  boundEffect : EffectLanguage
  bodyEffect : EffectLanguage
  boundTyping : HasLanguageComp sig ctx bound boundTy boundEffect
  bodyTyping : HasLanguageComp sig (boundTy :: ctx) body resultTy bodyEffect
  composedBelow : EffectLanguage.seq boundEffect bodyEffect ≤ effect

def HasLanguageComp.letView
    (typing : HasLanguageComp sig ctx (.letE bound body) resultTy effect) :
    LanguageLetView typing := by
  cases typing with
  | letE boundTyping bodyTyping =>
      exact ⟨_, _, _, boundTyping, bodyTyping, EffectLanguage.le_refl _⟩
  | subeffect inner upperBound =>
      let view := inner.letView
      exact ⟨view.boundTy, view.boundEffect, view.bodyEffect,
        view.boundTyping, view.bodyTyping,
        EffectLanguage.le_trans view.composedBelow upperBound⟩

structure LanguageFreeOpView
    (typing : HasLanguageComp sig ctx
      (.freeOp interface operation parameter) resultTy effect) where
  parameterTy : LanguageTy
  declaredResult : LanguageTy
  lookup : sig.free interface operation =
    some ⟨parameterTy, declaredResult⟩
  parameterTyping : HasLanguageVal sig ctx parameter parameterTy
  resultEq : declaredResult = resultTy
  requestBelow : principal [EffectAtom.free interface] ≤ effect

def HasLanguageComp.freeOpView
    (typing : HasLanguageComp sig ctx
      (.freeOp interface operation parameter) resultTy effect) :
    LanguageFreeOpView typing := by
  cases typing with
  | freeOp lookup parameterTyping =>
      exact ⟨_, _, lookup, parameterTyping, rfl, EffectLanguage.le_refl _⟩
  | subeffect inner upperBound =>
      let view := inner.freeOpView
      exact ⟨view.parameterTy, view.declaredResult, view.lookup,
        view.parameterTyping, view.resultEq,
        EffectLanguage.le_trans view.requestBelow upperBound⟩

structure LanguageBaseOpView
    (typing : HasLanguageComp sig ctx
      (.baseOp operation parameter) resultTy effect) where
  parameterTy : LanguageTy
  declaredResult : LanguageTy
  lookup : sig.base operation = some ⟨parameterTy, declaredResult⟩
  parameterTyping : HasLanguageVal sig ctx parameter parameterTy
  resultEq : declaredResult = resultTy
  requestBelow : principal [EffectAtom.base operation] ≤ effect

def HasLanguageComp.baseOpView
    (typing : HasLanguageComp sig ctx
      (.baseOp operation parameter) resultTy effect) :
    LanguageBaseOpView typing := by
  cases typing with
  | baseOp lookup parameterTyping =>
      exact ⟨_, _, lookup, parameterTyping, rfl, EffectLanguage.le_refl _⟩
  | subeffect inner upperBound =>
      let view := inner.baseOpView
      exact ⟨view.parameterTy, view.declaredResult, view.lookup,
        view.parameterTyping, view.resultEq,
        EffectLanguage.le_trans view.requestBelow upperBound⟩

/-- Typing of an evaluation context, frames innermost first. -/
inductive HasLanguageEvalContext (sig : LanguageSignature)
    (ctx : LanguageContext) : LanguageEvalContext →
    LanguageTy → EffectLanguage → LanguageTy → EffectLanguage → Type where
  | hole : HasLanguageEvalContext sig ctx [] holeTy holeEffect holeTy holeEffect
  | letE :
      HasLanguageComp sig (holeTy :: ctx) body frameTy bodyEffect →
      EffectLanguage.seq holeEffect bodyEffect ≤ frameEffect →
      HasLanguageEvalContext sig ctx rest frameTy frameEffect resultTy resultEffect →
      HasLanguageEvalContext sig ctx (.letE body :: rest)
        holeTy holeEffect resultTy resultEffect

def HasLanguageEvalContext.plugTyping
    (contextTyping : HasLanguageEvalContext sig ctx evalCtx
      holeTy holeEffect resultTy resultEffect)
    (termTyping : HasLanguageComp sig ctx term holeTy holeEffect) :
    HasLanguageComp sig ctx (LanguageEvalContext.plug evalCtx term)
      resultTy resultEffect :=
  match contextTyping with
  | .hole => termTyping
  | .letE bodyTyping bound restTyping =>
      restTyping.plugTyping ((HasLanguageComp.letE termTyping bodyTyping).subeffect bound)

/-- A context is non-erasing when every sequential suffix admits the empty
trace.  This is the exact local premise missing from unconditional
empty-free-effect safety. -/
def HasLanguageEvalContext.NonErasing :
    HasLanguageEvalContext sig ctx evalCtx holeTy holeEffect resultTy resultEffect → Prop
  | .hole => True
  | .letE (bodyEffect := bodyEffect) _ _ rest =>
      bodyEffect.contains 1 ∧ rest.NonErasing

theorem HasLanguageEvalContext.propagates_of_nonErasing
    (contextTyping : HasLanguageEvalContext sig ctx evalCtx
      holeTy holeEffect resultTy resultEffect)
    (nonErasing : contextTyping.NonErasing)
    (member : holeEffect.contains trace) : resultEffect.contains trace := by
  induction contextTyping with
  | hole => exact member
  | letE bodyTyping frameBound restTyping ih =>
      exact ih nonErasing.2
        (frameBound trace (EffectLanguage.le_seq_of_one_right nonErasing.1 trace member))

structure LanguagePlugView
    {evalCtx : LanguageEvalContext} {hole : FinLanguageComp}
    (typing : HasLanguageComp sig ctx
      (LanguageEvalContext.plug evalCtx hole) resultTy resultEffect) where
  holeTy : LanguageTy
  holeEffect : EffectLanguage
  holeTyping : HasLanguageComp sig ctx hole holeTy holeEffect
  contextTyping : HasLanguageEvalContext sig ctx evalCtx
    holeTy holeEffect resultTy resultEffect

def HasLanguageComp.plugView
    {evalCtx : LanguageEvalContext} {hole : FinLanguageComp}
    (typing : HasLanguageComp sig ctx
      (LanguageEvalContext.plug evalCtx hole) resultTy resultEffect) :
    LanguagePlugView typing :=
  match evalCtx with
  | [] => ⟨resultTy, resultEffect, typing, .hole⟩
  | .letE _ :: rest =>
      let outer := typing.plugView (evalCtx := rest)
      let frame := outer.holeTyping.letView
      ⟨frame.boundTy, frame.boundEffect, frame.boundTyping,
        .letE frame.bodyTyping frame.composedBelow outer.contextTyping⟩

structure TypedLanguageFreeRequest
    {request : LanguageFreeRequest}
    (typing : HasLanguageComp sig ctx request.source resultTy resultEffect) where
  parameterTy : LanguageTy
  responseTy : LanguageTy
  holeEffect : EffectLanguage
  lookup : sig.free request.interface request.operation =
    some ⟨parameterTy, responseTy⟩
  parameterTyping : HasLanguageVal sig ctx request.parameter parameterTy
  contextTyping : HasLanguageEvalContext sig ctx request.context
    responseTy holeEffect resultTy resultEffect
  requestBelowHole : principal [EffectAtom.free request.interface] ≤ holeEffect

def HasLanguageComp.exposedFreeView
    {request : LanguageFreeRequest}
    (typing : HasLanguageComp sig ctx request.source resultTy resultEffect) :
    TypedLanguageFreeRequest typing := by
  let plugged := typing.plugView (evalCtx := request.context)
  let operation := plugged.holeTyping.freeOpView
  rcases operation with ⟨parameterTy, declaredResult, lookup,
    parameterTyping, resultEq, requestBelow⟩
  cases resultEq
  exact ⟨parameterTy, plugged.holeTy, plugged.holeEffect, lookup,
    parameterTyping, plugged.contextTyping, requestBelow⟩

/-- Under the non-erasing continuation premise, the interface atom of an
exposed request is visible in the whole computation's declared language. -/
theorem TypedLanguageFreeRequest.interface_visible
    {request : LanguageFreeRequest}
    {typing : HasLanguageComp sig ctx request.source resultTy resultEffect}
    (requestTyping : TypedLanguageFreeRequest typing)
    (nonErasing : requestTyping.contextTyping.NonErasing) :
    resultEffect.contains [EffectAtom.free request.interface] := by
  apply requestTyping.contextTyping.propagates_of_nonErasing nonErasing
  exact requestTyping.requestBelowHole _ (Effect.le_refl _)

theorem TypedLanguageFreeRequest.not_exposed_of_interface_absent
    {request : LanguageFreeRequest}
    {typing : HasLanguageComp sig ctx request.source resultTy resultEffect}
    (requestTyping : TypedLanguageFreeRequest typing)
    (nonErasing : requestTyping.contextTyping.NonErasing)
    (absent : ∀ trace, resultEffect.contains trace →
      EffectAtom.free request.interface ∉ trace) : False := by
  exact absent _ (requestTyping.interface_visible nonErasing) (by simp)

structure TypedLanguageBaseRequest
    {request : LanguageBaseRequest}
    (typing : HasLanguageComp sig ctx request.source resultTy resultEffect) where
  parameterTy : LanguageTy
  responseTy : LanguageTy
  holeEffect : EffectLanguage
  lookup : sig.base request.operation = some ⟨parameterTy, responseTy⟩
  parameterTyping : HasLanguageVal sig ctx request.parameter parameterTy
  contextTyping : HasLanguageEvalContext sig ctx request.context
    responseTy holeEffect resultTy resultEffect
  requestBelowHole : principal [EffectAtom.base request.operation] ≤ holeEffect

def HasLanguageComp.exposedBaseView
    {request : LanguageBaseRequest}
    (typing : HasLanguageComp sig ctx request.source resultTy resultEffect) :
    TypedLanguageBaseRequest typing := by
  let plugged := typing.plugView (evalCtx := request.context)
  let operation := plugged.holeTyping.baseOpView
  rcases operation with ⟨parameterTy, declaredResult, lookup,
    parameterTyping, resultEq, requestBelow⟩
  cases resultEq
  exact ⟨parameterTy, plugged.holeTy, plugged.holeEffect, lookup,
    parameterTyping, plugged.contextTyping, requestBelow⟩

def TypedLanguageFreeRequest.resumeTyping
    {request : LanguageFreeRequest}
    {typing : HasLanguageComp sig ctx request.source resultTy resultEffect}
    (requestTyping : TypedLanguageFreeRequest typing)
    (responseTyping : HasLanguageVal sig ctx response requestTyping.responseTy) :
    HasLanguageComp sig ctx (request.resume response) resultTy resultEffect :=
  requestTyping.contextTyping.plugTyping
    ((HasLanguageComp.ret responseTyping).subeffect
      (EffectLanguage.le_trans
        (EffectLanguage.principal_mono
          (Effect.nil_le [EffectAtom.free request.interface]))
        requestTyping.requestBelowHole))

def TypedLanguageBaseRequest.resumeTyping
    {request : LanguageBaseRequest}
    {typing : HasLanguageComp sig ctx request.source resultTy resultEffect}
    (requestTyping : TypedLanguageBaseRequest typing)
    (responseTyping : HasLanguageVal sig ctx response requestTyping.responseTy) :
    HasLanguageComp sig ctx (request.resume response) resultTy resultEffect :=
  requestTyping.contextTyping.plugTyping
    ((HasLanguageComp.ret responseTyping).subeffect
      (EffectLanguage.le_trans
        (EffectLanguage.principal_mono
          (Effect.nil_le [EffectAtom.base request.operation]))
        requestTyping.requestBelowHole))

/-- Principal sequential suffix reconstructed from the actual context frames. -/
structure LanguagePrincipalFactor
    (contextTyping : HasLanguageEvalContext sig ctx evalCtx
      holeTy oldHole resultTy resultEffect)
    (headLanguage : EffectLanguage) (newHole : EffectLanguage) where
  suffix : EffectLanguage
  bound : EffectLanguage.seq headLanguage suffix ≤ resultEffect
  typing : HasLanguageEvalContext sig ctx evalCtx
    holeTy newHole resultTy (EffectLanguage.seq newHole suffix)

def HasLanguageEvalContext.principalFactor
    (contextTyping : HasLanguageEvalContext sig ctx evalCtx
      holeTy oldHole resultTy resultEffect)
    (headBelow : headLanguage ≤ oldHole) :
    LanguagePrincipalFactor contextTyping headLanguage newHole :=
  match contextTyping with
  | .hole => ⟨principal 1, by
      rw [EffectLanguage.seq_one_right]
      exact headBelow,
      by
        rw [EffectLanguage.seq_one_right]
        exact (HasLanguageEvalContext.hole :
          HasLanguageEvalContext sig ctx [] holeTy newHole holeTy newHole)⟩
  | .letE (bodyEffect := bodyEffect) bodyTyping frameBound restTyping =>
      let nextBelow := EffectLanguage.le_trans
        (EffectLanguage.seq_mono headBelow (EffectLanguage.le_refl bodyEffect))
        frameBound
      let restFactor := restTyping.principalFactor
        (newHole := EffectLanguage.seq newHole bodyEffect) nextBelow
      ⟨EffectLanguage.seq bodyEffect restFactor.suffix,
        by simpa only [EffectLanguage.seq_assoc] using restFactor.bound,
        by simpa only [EffectLanguage.seq_assoc] using
          HasLanguageEvalContext.letE bodyTyping (EffectLanguage.le_refl _)
            restFactor.typing⟩

end EffectSemantics
