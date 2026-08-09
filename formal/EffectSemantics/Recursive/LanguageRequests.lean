import EffectSemantics.Examples.LanguageRecursion

namespace EffectSemantics

inductive RecLanguageFrame where
  | letE (body : RecLanguageComp)

abbrev RecLanguageEvalContext := List RecLanguageFrame

def RecLanguageFrame.plug : RecLanguageFrame → RecLanguageComp → RecLanguageComp
  | .letE body, bound => .letE bound body

def RecLanguageEvalContext.plug :
    RecLanguageEvalContext → RecLanguageComp → RecLanguageComp
  | [], term => term
  | frame :: rest, term =>
      RecLanguageEvalContext.plug rest (frame.plug term)

theorem RecLanguageEvalContext.plug_append
    (left right : RecLanguageEvalContext) (term : RecLanguageComp) :
    RecLanguageEvalContext.plug (left ++ right) term =
      RecLanguageEvalContext.plug right (RecLanguageEvalContext.plug left term) := by
  induction left generalizing term with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.cons_append, RecLanguageEvalContext.plug]
      exact ih (frame.plug term)

structure RecLanguageFreeRequest where
  interface : Nat
  operation : Nat
  parameter : RecLanguageVal
  context : RecLanguageEvalContext

def RecLanguageFreeRequest.source (request : RecLanguageFreeRequest) :
    RecLanguageComp :=
  request.context.plug (.freeOp request.interface request.operation request.parameter)

def RecLanguageFreeRequest.resume (request : RecLanguageFreeRequest)
    (response : RecLanguageVal) : RecLanguageComp :=
  request.context.plug (.ret response)

def RecLanguageFreeRequest.outerLet (request : RecLanguageFreeRequest)
    (body : RecLanguageComp) : RecLanguageFreeRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem RecLanguageFreeRequest.outerLet_source
    (request : RecLanguageFreeRequest) (body : RecLanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold RecLanguageFreeRequest.outerLet RecLanguageFreeRequest.source
  rw [RecLanguageEvalContext.plug_append]
  rfl

structure RecLanguageBaseRequest where
  operation : Nat
  parameter : RecLanguageVal
  context : RecLanguageEvalContext

def RecLanguageBaseRequest.source (request : RecLanguageBaseRequest) :
    RecLanguageComp :=
  request.context.plug (.baseOp request.operation request.parameter)

def RecLanguageBaseRequest.resume (request : RecLanguageBaseRequest)
    (response : RecLanguageVal) : RecLanguageComp :=
  request.context.plug (.ret response)

def RecLanguageBaseRequest.outerLet (request : RecLanguageBaseRequest)
    (body : RecLanguageComp) : RecLanguageBaseRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem RecLanguageBaseRequest.outerLet_source
    (request : RecLanguageBaseRequest) (body : RecLanguageComp) :
    (request.outerLet body).source = .letE request.source body := by
  unfold RecLanguageBaseRequest.outerLet RecLanguageBaseRequest.source
  rw [RecLanguageEvalContext.plug_append]
  rfl

def RecLanguageFrame.rename (rename : Nat → Nat) :
    RecLanguageFrame → RecLanguageFrame
  | .letE body => .letE (body.rename (liftLanguageRen rename))

def RecLanguageEvalContext.rename (rename : Nat → Nat)
    (context : RecLanguageEvalContext) : RecLanguageEvalContext :=
  context.map (RecLanguageFrame.rename rename)

def RecLanguageFreeRequest.answerWith (request : RecLanguageFreeRequest)
    (clause : RecLanguageComp) : RecLanguageComp :=
  .letE (clause.subst0 request.parameter)
    ((request.context.rename (fun index => index + 1)).plug (.ret (.var 0)))

inductive RecLanguageHead where
  | returned (value : RecLanguageVal)
  | internal (next : RecLanguageComp)
  | base (request : RecLanguageBaseRequest)
  | free (request : RecLanguageFreeRequest)
  | stuck

def RecLanguageComp.head : RecLanguageComp → RecLanguageHead
  | .ret value => .returned value
  | .letE bound body =>
      match RecLanguageComp.head bound with
      | .returned value => .internal (body.subst0 value)
      | .internal next => .internal (.letE next body)
      | .base request => .base (request.outerLet body)
      | .free request => .free (request.outerLet body)
      | .stuck => .stuck
  | .app (.lam _ _ body) argument => .internal (body.subst0 argument)
  | .app (.fixLam allowed domain latent body) argument =>
      .internal (body.subst2 argument (.fixLam allowed domain latent body))
  | .app _ _ => .stuck
  | .ite (.bool true) thenBranch _ => .internal thenBranch
  | .ite (.bool false) _ elseBranch => .internal elseBranch
  | .ite _ _ _ => .stuck
  | .case (.inl value _) leftBranch _ => .internal (leftBranch.subst0 value)
  | .case (.inr _ value) _ rightBranch => .internal (rightBranch.subst0 value)
  | .case _ _ _ => .stuck
  | .baseOp operation parameter => .base ⟨operation, parameter, []⟩
  | .freeOp interface operation parameter =>
      .free ⟨interface, operation, parameter, []⟩

theorem LanguageStep.to_recHead
    (step : LanguageStep (mode := .recursive) term next) :
    RecLanguageComp.head term = .internal next := by
  induction step with
  | letReturn | beta | fixBeta | ifTrue | ifFalse | caseInl | caseInr => rfl
  | underLet inner ih => simp [RecLanguageComp.head, ih]

theorem RecLanguageEvalContext.plug_head_base
    (context : RecLanguageEvalContext)
    (head : RecLanguageComp.head term = .base request) :
    RecLanguageComp.head (context.plug term) =
      .base { request with context := request.context ++ context } := by
  induction context generalizing term request with
  | nil => cases request; simpa [RecLanguageEvalContext.plug] using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          have inner : RecLanguageComp.head (.letE term body) =
              .base (request.outerLet body) := by
            simp [RecLanguageComp.head, head]
          simpa [RecLanguageEvalContext.plug, RecLanguageFrame.plug,
            RecLanguageBaseRequest.outerLet,
            List.append_assoc] using ih inner

theorem RecLanguageEvalContext.plug_head_free
    (context : RecLanguageEvalContext)
    (head : RecLanguageComp.head term = .free request) :
    RecLanguageComp.head (context.plug term) =
      .free { request with context := request.context ++ context } := by
  induction context generalizing term request with
  | nil => cases request; simpa [RecLanguageEvalContext.plug] using head
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          have inner : RecLanguageComp.head (.letE term body) =
              .free (request.outerLet body) := by
            simp [RecLanguageComp.head, head]
          simpa [RecLanguageEvalContext.plug, RecLanguageFrame.plug,
            RecLanguageFreeRequest.outerLet,
            List.append_assoc] using ih inner

@[simp] theorem RecLanguageBaseRequest.source_head
    (request : RecLanguageBaseRequest) :
    RecLanguageComp.head request.source = .base request := by
  cases request with
  | mk operation parameter context =>
      simpa [RecLanguageBaseRequest.source] using
        RecLanguageEvalContext.plug_head_base context
          (term := LanguageComp.baseOp operation parameter)
          (request := RecLanguageBaseRequest.mk operation parameter []) rfl

@[simp] theorem RecLanguageFreeRequest.source_head
    (request : RecLanguageFreeRequest) :
    RecLanguageComp.head request.source = .free request := by
  cases request with
  | mk interface operation parameter context =>
      simpa [RecLanguageFreeRequest.source] using
        RecLanguageEvalContext.plug_head_free context
          (term := LanguageComp.freeOp interface operation parameter)
          (request := RecLanguageFreeRequest.mk interface operation parameter []) rfl

mutual
  theorem RecLanguageComp.head_returned_sound
      {term : RecLanguageComp} {value : RecLanguageVal}
      (equal : term.head = .returned value) : term = .ret value := by
    cases term with
    | ret result => simp [RecLanguageComp.head] at equal; cases equal; rfl
    | letE bound body =>
        cases found : RecLanguageComp.head bound <;> simp [RecLanguageComp.head, found] at equal
    | app function argument => cases function <;> simp [RecLanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [RecLanguageComp.head] at equal
        | _ => simp [RecLanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [RecLanguageComp.head] at equal
    | baseOp operation parameter => simp [RecLanguageComp.head] at equal
    | freeOp interface operation parameter => simp [RecLanguageComp.head] at equal

  theorem RecLanguageComp.head_internal_sound
      {term next : RecLanguageComp} (equal : term.head = .internal next) :
      Nonempty (LanguageStep term next) := by
    cases term with
    | ret value => simp [RecLanguageComp.head] at equal
    | letE bound body =>
        cases found : RecLanguageComp.head bound with
        | returned value =>
            have source := RecLanguageComp.head_returned_sound found
            subst bound
            simp [RecLanguageComp.head] at equal
            subst next
            exact ⟨.letReturn⟩
        | internal inner =>
            simp [RecLanguageComp.head, found] at equal
            subst next
            obtain ⟨step⟩ := RecLanguageComp.head_internal_sound found
            exact ⟨.underLet step⟩
        | base request | free request | stuck =>
            simp [RecLanguageComp.head, found] at equal
    | app function argument =>
        cases function <;> simp [RecLanguageComp.head] at equal
        · subst next; exact ⟨.beta⟩
        · subst next; exact ⟨.fixBeta⟩
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag =>
            cases flag <;> simp [RecLanguageComp.head] at equal
            · subst next; exact ⟨.ifFalse⟩
            · subst next; exact ⟨.ifTrue⟩
        | _ => simp [RecLanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [RecLanguageComp.head] at equal
        · subst next; exact ⟨.caseInl⟩
        · subst next; exact ⟨.caseInr⟩
    | baseOp operation parameter => simp [RecLanguageComp.head] at equal
    | freeOp interface operation parameter => simp [RecLanguageComp.head] at equal

  theorem RecLanguageComp.head_base_sound
      {term : RecLanguageComp} {request : RecLanguageBaseRequest}
      (equal : term.head = .base request) : term = request.source := by
    cases term with
    | ret value => simp [RecLanguageComp.head] at equal
    | letE bound body =>
        cases found : RecLanguageComp.head bound with
        | base inner =>
            simp [RecLanguageComp.head, found] at equal
            subst request
            rw [RecLanguageComp.head_base_sound found,
              RecLanguageBaseRequest.outerLet_source]
        | _ => simp [RecLanguageComp.head, found] at equal
    | app function argument => cases function <;> simp [RecLanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [RecLanguageComp.head] at equal
        | _ => simp [RecLanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [RecLanguageComp.head] at equal
    | baseOp operation parameter =>
        simp [RecLanguageComp.head] at equal
        subst request
        rfl
    | freeOp interface operation parameter => simp [RecLanguageComp.head] at equal

  theorem RecLanguageComp.head_free_sound
      {term : RecLanguageComp} {request : RecLanguageFreeRequest}
      (equal : term.head = .free request) : term = request.source := by
    cases term with
    | ret value => simp [RecLanguageComp.head] at equal
    | letE bound body =>
        cases found : RecLanguageComp.head bound with
        | free inner =>
            simp [RecLanguageComp.head, found] at equal
            subst request
            rw [RecLanguageComp.head_free_sound found,
              RecLanguageFreeRequest.outerLet_source]
        | _ => simp [RecLanguageComp.head, found] at equal
    | app function argument => cases function <;> simp [RecLanguageComp.head] at equal
    | ite condition thenBranch elseBranch =>
        cases condition with
        | bool flag => cases flag <;> simp [RecLanguageComp.head] at equal
        | _ => simp [RecLanguageComp.head] at equal
    | case scrutinee leftBranch rightBranch =>
        cases scrutinee <;> simp [RecLanguageComp.head] at equal
    | baseOp operation parameter => simp [RecLanguageComp.head] at equal
    | freeOp interface operation parameter =>
        simp [RecLanguageComp.head] at equal
        subst request
        rfl
end

end EffectSemantics
