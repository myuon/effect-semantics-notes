import EffectSemantics.Metatheory.LanguageProgress

namespace EffectSemantics

open EffectLanguage

inductive LanguageFrame where
  | letE (body : LanguageComp)

abbrev LanguageEvalContext := List LanguageFrame

def LanguageFrame.plug : LanguageFrame → LanguageComp → LanguageComp
  | .letE body, bound => .letE bound body

def LanguageEvalContext.plug : LanguageEvalContext → LanguageComp → LanguageComp
  | [], term => term
  | frame :: rest, term =>
      LanguageEvalContext.plug rest (frame.plug term)

theorem LanguageEvalContext.plug_append
    (left right : LanguageEvalContext) (term : LanguageComp) :
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

structure LanguageFreeRequest where
  interface : Nat
  operation : Nat
  parameter : LanguageVal
  context : LanguageEvalContext

def LanguageFreeRequest.source (request : LanguageFreeRequest) : LanguageComp :=
  LanguageEvalContext.plug request.context
    (.freeOp request.interface request.operation request.parameter)

def LanguageFreeRequest.openResume (request : LanguageFreeRequest) :
    LanguageComp :=
  LanguageEvalContext.plug
    (LanguageEvalContext.rename (· + 1) request.context) (.ret (.var 0))

def LanguageFreeRequest.resume (request : LanguageFreeRequest)
    (response : LanguageVal) : LanguageComp :=
  LanguageEvalContext.plug request.context (.ret response)

def LanguageFreeRequest.outerLet (request : LanguageFreeRequest)
    (body : LanguageComp) : LanguageFreeRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem LanguageFreeRequest.outerLet_source
    (request : LanguageFreeRequest) (body : LanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold LanguageFreeRequest.outerLet LanguageFreeRequest.source
  rw [LanguageEvalContext.plug_append]
  rfl

structure LanguageBaseRequest where
  operation : Nat
  parameter : LanguageVal
  context : LanguageEvalContext

def LanguageBaseRequest.source (request : LanguageBaseRequest) : LanguageComp :=
  LanguageEvalContext.plug request.context
    (.baseOp request.operation request.parameter)

def LanguageBaseRequest.resume (request : LanguageBaseRequest)
    (response : LanguageVal) : LanguageComp :=
  LanguageEvalContext.plug request.context (.ret response)

def LanguageBaseRequest.outerLet (request : LanguageBaseRequest)
    (body : LanguageComp) : LanguageBaseRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem LanguageBaseRequest.outerLet_source
    (request : LanguageBaseRequest) (body : LanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold LanguageBaseRequest.outerLet LanguageBaseRequest.source
  rw [LanguageEvalContext.plug_append]
  rfl

inductive LanguageBoundaryView : LanguageComp → Type where
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

structure LanguagePlugView
    {evalCtx : LanguageEvalContext} {hole : LanguageComp}
    (typing : HasLanguageComp sig ctx
      (LanguageEvalContext.plug evalCtx hole) resultTy resultEffect) where
  holeTy : LanguageTy
  holeEffect : EffectLanguage
  holeTyping : HasLanguageComp sig ctx hole holeTy holeEffect
  contextTyping : HasLanguageEvalContext sig ctx evalCtx
    holeTy holeEffect resultTy resultEffect

def HasLanguageComp.plugView
    {evalCtx : LanguageEvalContext} {hole : LanguageComp}
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
