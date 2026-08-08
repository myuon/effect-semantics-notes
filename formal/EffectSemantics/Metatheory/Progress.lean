import EffectSemantics.Metatheory.RequestDecomposition

namespace EffectSemantics

def FreeRequest.outerLet (request : FreeRequest) (body : Comp) : FreeRequest :=
  { request with context := request.context ++ [.letE body] }

def BaseRequest.outerLet (request : BaseRequest) (body : Comp) : BaseRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem FreeRequest.outerLet_source (request : FreeRequest) (body : Comp) :
    (request.outerLet body).source = .letE request.source body := by
  simp [FreeRequest.outerLet, FreeRequest.source, EvalContext.plug_append,
    Frame.plug]

@[simp] theorem BaseRequest.outerLet_source (request : BaseRequest) (body : Comp) :
    (request.outerLet body).source = .letE request.source body := by
  simp [BaseRequest.outerLet, BaseRequest.source, EvalContext.plug_append,
    Frame.plug]

/-- The four observable states of a closed fine-grain computation. -/
inductive Progress : Comp → Type where
  | returned (value : Val) : Progress (.ret value)
  | internal {term term' : Comp} : Step term term' → Progress term
  | base (request : BaseRequest) : Progress request.source
  | free (request : FreeRequest) : Progress request.source

def HasComp.progressClosed {sig : Signature} {term : Comp} {ty : Ty}
    {effect : Effect} (typing : HasComp sig [] term ty effect) : Progress term :=
  match typing with
  | .subeffect inner _ => inner.progressClosed
  | .ret _ => .returned _
  | .baseOp _ _ => .base ⟨_, _, []⟩
  | .freeOp _ _ => .free ⟨_, _, _, []⟩
  | .letE boundTyping _ =>
      match boundTyping.progressClosed with
      | .returned _ => .internal .letReturn
      | .internal step => .internal (.underLet step)
      | .base request => by simpa using Progress.base (request.outerLet _)
      | .free request => by simpa using Progress.free (request.outerLet _)
  | .app functionTyping _ =>
      match functionTyping with
      | .var lookup => nomatch lookup
      | .lam _ => .internal .beta
      | .fixLam _ => .internal .fixBeta
  | .ite conditionTyping _ _ =>
      match conditionTyping with
      | .var lookup => nomatch lookup
      | .bool (value := true) => .internal .ifTrue
      | .bool (value := false) => .internal .ifFalse
  | .case scrutineeTyping _ _ =>
      match scrutineeTyping with
      | .var lookup => nomatch lookup
      | .inl _ => .internal .caseInl
      | .inr _ => .internal .caseInr

theorem Step.deterministic {term left right : Comp}
    (first : Step term left) (second : Step term right) : left = right := by
  have firstEq := first.to_internalStep
  have secondEq := second.to_internalStep
  rw [firstEq] at secondEq
  exact Option.some.inj secondEq

end EffectSemantics
