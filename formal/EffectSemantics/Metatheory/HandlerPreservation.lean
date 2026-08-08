import EffectSemantics.Syntax.HandlerTyping

namespace EffectSemantics

/-- Typing invariant on the two sides of a sharp affine-handler transition. -/
inductive HasSharpState (sig : Signature) (ctx : Context)
    (interface : Nat) (handler : AffineHandler) (clauseEffect pre post : Effect)
    (resultTy : Ty) : HandlerState → Type where
  | pending : HasComp sig ctx term resultTy
      (pre * [EffectAtom.free interface] * post) →
      HasSharpState sig ctx interface handler clauseEffect pre post resultTy
        (.shallow interface handler term)
  | done : HasComp sig ctx term resultTy (pre * clauseEffect * post) →
      HasSharpState sig ctx interface handler clauseEffect pre post resultTy
        (.core term)

/-- Internal, return and matching shallow transitions all preserve the sharp
two-phase typing invariant. -/
def ShallowStep.preserveSharp
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect pre post : Effect}
    {resultTy : Ty} {state next : HandlerState}
    (handlerTyping : HasAffineHandler sig ctx interface handler clauseEffect)
    (preFree : Effect.FreeOf interface pre)
    (step : ShallowStep state next)
    (typing : HasSharpState sig ctx interface handler clauseEffect pre post
      resultTy state) :
    HasSharpState sig ctx interface handler clauseEffect pre post resultTy next := by
  cases step with
  | internal sourceStep =>
      cases typing with
      | pending termTyping => exact .pending (sourceStep.preserve termTyping)
  | returned =>
      cases typing with
      | pending termTyping =>
          let view := termTyping.returnView
          exact .done ((HasComp.ret view.valueTyping).subeffect (Effect.nil_le _))
  | matched exposed same found =>
      cases typing with
      | pending termTyping =>
          exact .done (handlerTyping.answerWithTypingSharp
            (exposed ▸ termTyping) same preFree found)

/-- Transparent forwarding preserves the pending phase: after the environment
supplies a well-typed response, the original residual context is reconstructed
and the same shallow handler is reinstalled. -/
def ShallowBoundary.resumeBasePreserveSharp
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect pre post : Effect}
    {resultTy parameterTy responseTy : Ty} {request : BaseRequest}
    (typing : HasSharpState sig ctx interface handler clauseEffect pre post
      resultTy (.shallow interface handler request.source))
    (lookup : sig.base request.operation = some ⟨parameterTy, responseTy⟩)
    (responseTyping : HasVal sig ctx response responseTy) :
    HasSharpState sig ctx interface handler clauseEffect pre post resultTy
      (.shallow interface handler (request.resume response)) := by
  cases typing with
  | pending termTyping =>
      let requestTyping := termTyping.exposedBaseView
      have declarationEq := Signature.base_lookup_unique
        requestTyping.lookup lookup
      cases declarationEq
      exact @HasSharpState.pending sig ctx interface handler clauseEffect pre post
        resultTy _ (requestTyping.resumeTyping responseTyping)

def ShallowBoundary.resumeFreeOtherPreserveSharp
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect pre post : Effect}
    {resultTy parameterTy responseTy : Ty} {request : FreeRequest}
    (_different : request.interface ≠ interface)
    (typing : HasSharpState sig ctx interface handler clauseEffect pre post
      resultTy (.shallow interface handler request.source))
    (lookup : sig.free request.interface request.operation =
      some ⟨parameterTy, responseTy⟩)
    (responseTyping : HasVal sig ctx response responseTy) :
    HasSharpState sig ctx interface handler clauseEffect pre post resultTy
      (.shallow interface handler (request.resume response)) := by
  cases typing with
  | pending termTyping =>
      let requestTyping := termTyping.exposedFreeView
      have declarationEq := Signature.free_lookup_unique
        requestTyping.lookup lookup
      cases declarationEq
      exact @HasSharpState.pending sig ctx interface handler clauseEffect pre post
        resultTy _ (requestTyping.resumeTyping responseTyping)

def ShallowBoundary.resumeFreeMissingPreserveSharp
    {sig : Signature} {ctx : Context} {interface : Nat}
    {handler : AffineHandler} {clauseEffect pre post : Effect}
    {resultTy parameterTy responseTy : Ty} {request : FreeRequest}
    (_same : request.interface = interface)
    (_missing : handler.lookup request.operation = none)
    (typing : HasSharpState sig ctx interface handler clauseEffect pre post
      resultTy (.shallow interface handler request.source))
    (lookup : sig.free request.interface request.operation =
      some ⟨parameterTy, responseTy⟩)
    (responseTyping : HasVal sig ctx response responseTy) :
    HasSharpState sig ctx interface handler clauseEffect pre post resultTy
      (.shallow interface handler (request.resume response)) := by
  cases typing with
  | pending termTyping =>
      let requestTyping := termTyping.exposedFreeView
      have declarationEq := Signature.free_lookup_unique
        requestTyping.lookup lookup
      cases declarationEq
      exact @HasSharpState.pending sig ctx interface handler clauseEffect pre post
        resultTy _ (requestTyping.resumeTyping responseTyping)

/-- Exhaustiveness rules out the same-interface missing-clause boundary for
every operation actually declared by the signature. -/
theorem AffineHandler.exhaustive_not_missing
    {sig : Signature} {interface operation : Nat}
    {handler : AffineHandler} {parameterTy responseTy : Ty}
    (exhaustive : handler.Exhaustive sig interface)
    (lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩)
    (missing : handler.lookup operation = none) : False := by
  obtain ⟨clause, found⟩ := exhaustive operation parameterTy responseTy lookup
  rw [missing] at found
  contradiction

end EffectSemantics
