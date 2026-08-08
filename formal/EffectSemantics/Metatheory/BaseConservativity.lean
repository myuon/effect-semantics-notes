import EffectSemantics.Recursive.FiniteObservation

namespace EffectSemantics

set_option linter.defProp false in
mutual
  def Val.BaseOnly : Val → Prop
    | .var _ | .unit | .bool _ => True
    | .pair left right => left.BaseOnly ∧ right.BaseOnly
    | .inl value _ | .inr _ value => value.BaseOnly
    | .lam _ _ body | .fixLam _ _ body => body.BaseOnly

  def Comp.BaseOnly : Comp → Prop
    | .ret value => value.BaseOnly
    | .letE bound body => bound.BaseOnly ∧ body.BaseOnly
    | .app function argument => function.BaseOnly ∧ argument.BaseOnly
    | .ite condition thenBranch elseBranch =>
        condition.BaseOnly ∧ thenBranch.BaseOnly ∧ elseBranch.BaseOnly
    | .case scrutinee leftBranch rightBranch =>
        scrutinee.BaseOnly ∧ leftBranch.BaseOnly ∧ rightBranch.BaseOnly
    | .baseOp _ parameter => parameter.BaseOnly
    | .freeOp _ _ _ => False
end

def BaseOnlySubstitution (substitution : Nat → Val) : Prop :=
  ∀ index, (substitution index).BaseOnly

mutual
  theorem Val.baseOnly_rename {value : Val} {rename : Nat → Nat}
      (baseOnly : value.BaseOnly) :
      (value.rename rename).BaseOnly := by
    cases value with
    | var | unit | bool => trivial
    | pair left right =>
        exact ⟨left.baseOnly_rename baseOnly.1,
          right.baseOnly_rename baseOnly.2⟩
    | inl value rightTy => exact value.baseOnly_rename baseOnly
    | inr leftTy value => exact value.baseOnly_rename baseOnly
    | lam domain latent body => exact body.baseOnly_rename baseOnly
    | fixLam domain latent body => exact body.baseOnly_rename baseOnly

  theorem Comp.baseOnly_rename {term : Comp} {rename : Nat → Nat}
      (baseOnly : term.BaseOnly) :
      (term.rename rename).BaseOnly := by
    cases term with
    | ret value => exact value.baseOnly_rename baseOnly
    | letE bound body =>
        exact ⟨bound.baseOnly_rename baseOnly.1,
          body.baseOnly_rename baseOnly.2⟩
    | app function argument =>
        exact ⟨function.baseOnly_rename baseOnly.1,
          argument.baseOnly_rename baseOnly.2⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨condition.baseOnly_rename baseOnly.1,
          thenBranch.baseOnly_rename baseOnly.2.1,
          elseBranch.baseOnly_rename baseOnly.2.2⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨scrutinee.baseOnly_rename baseOnly.1,
          leftBranch.baseOnly_rename baseOnly.2.1,
          rightBranch.baseOnly_rename baseOnly.2.2⟩
    | baseOp operation parameter => exact parameter.baseOnly_rename baseOnly
    | freeOp => contradiction
end

theorem BaseOnlySubstitution.lift (baseOnly : BaseOnlySubstitution substitution) :
    BaseOnlySubstitution (liftSubst substitution) := by
  intro index
  cases index with
  | zero => trivial
  | succ index => exact Val.baseOnly_rename (baseOnly index)

mutual
  theorem Val.baseOnly_subst {value : Val} {substitution : Nat → Val}
      (valueOnly : value.BaseOnly)
      (substitutionOnly : BaseOnlySubstitution substitution) :
      (value.subst substitution).BaseOnly := by
    cases value with
    | var index => exact substitutionOnly index
    | unit | bool => trivial
    | pair left right =>
        exact ⟨left.baseOnly_subst valueOnly.1 substitutionOnly,
          right.baseOnly_subst valueOnly.2 substitutionOnly⟩
    | inl value rightTy => exact value.baseOnly_subst valueOnly substitutionOnly
    | inr leftTy value => exact value.baseOnly_subst valueOnly substitutionOnly
    | lam domain latent body =>
        exact body.baseOnly_subst valueOnly substitutionOnly.lift
    | fixLam domain latent body =>
        exact body.baseOnly_subst valueOnly substitutionOnly.lift.lift

  theorem Comp.baseOnly_subst {term : Comp} {substitution : Nat → Val}
      (termOnly : term.BaseOnly)
      (substitutionOnly : BaseOnlySubstitution substitution) :
      (term.subst substitution).BaseOnly := by
    cases term with
    | ret value => exact value.baseOnly_subst termOnly substitutionOnly
    | letE bound body =>
        exact ⟨bound.baseOnly_subst termOnly.1 substitutionOnly,
          body.baseOnly_subst termOnly.2 substitutionOnly.lift⟩
    | app function argument =>
        exact ⟨function.baseOnly_subst termOnly.1 substitutionOnly,
          argument.baseOnly_subst termOnly.2 substitutionOnly⟩
    | ite condition thenBranch elseBranch =>
        exact ⟨condition.baseOnly_subst termOnly.1 substitutionOnly,
          thenBranch.baseOnly_subst termOnly.2.1 substitutionOnly,
          elseBranch.baseOnly_subst termOnly.2.2 substitutionOnly⟩
    | case scrutinee leftBranch rightBranch =>
        exact ⟨scrutinee.baseOnly_subst termOnly.1 substitutionOnly,
          leftBranch.baseOnly_subst termOnly.2.1 substitutionOnly.lift,
          rightBranch.baseOnly_subst termOnly.2.2 substitutionOnly.lift⟩
    | baseOp operation parameter =>
        exact parameter.baseOnly_subst termOnly substitutionOnly
    | freeOp => contradiction
end

theorem Comp.baseOnly_subst0 {body : Comp} {value : Val}
    (bodyOnly : body.BaseOnly)
    (valueOnly : value.BaseOnly) : (body.subst0 value).BaseOnly := by
  apply body.baseOnly_subst bodyOnly
  intro index
  cases index with
  | zero => exact valueOnly
  | succ index => trivial

theorem Comp.baseOnly_subst2 {body : Comp} {argument self : Val}
    (bodyOnly : body.BaseOnly)
    (argumentOnly : argument.BaseOnly) (selfOnly : self.BaseOnly) :
    (body.subst2 argument self).BaseOnly := by
  apply body.baseOnly_subst bodyOnly
  intro index
  cases index with
  | zero => exact argumentOnly
  | succ index =>
      cases index with
      | zero => exact selfOnly
      | succ index => trivial

/-- Internal evaluation of an old-language term cannot introduce a free
operation, including recursive unfolding and substitution. -/
theorem Step.preservesBaseOnly (step : Step term next)
    (baseOnly : term.BaseOnly) : next.BaseOnly := by
  cases step with
  | letReturn => exact Comp.baseOnly_subst0 baseOnly.2 baseOnly.1
  | beta => exact Comp.baseOnly_subst0 baseOnly.1 baseOnly.2
  | fixBeta => exact Comp.baseOnly_subst2 baseOnly.1 baseOnly.2 baseOnly.1
  | ifTrue => exact baseOnly.2.1
  | ifFalse => exact baseOnly.2.2
  | caseInl => exact Comp.baseOnly_subst0 baseOnly.2.1 baseOnly.1
  | caseInr => exact Comp.baseOnly_subst0 baseOnly.2.2 baseOnly.1
  | underLet inner => exact ⟨inner.preservesBaseOnly baseOnly.1, baseOnly.2⟩

theorem EvalContext.plug_not_baseOnly (ctx : EvalContext)
    (notBaseOnly : ¬ term.BaseOnly) : ¬ (ctx.plug term).BaseOnly := by
  induction ctx generalizing term with
  | nil => exact notBaseOnly
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          apply ih
          intro frameOnly
          exact notBaseOnly frameOnly.1

def EvalContextBaseOnly : EvalContext → Prop
  | [] => True
  | .letE body :: rest => body.BaseOnly ∧ EvalContextBaseOnly rest

theorem EvalContext.plug_baseOnly_iff (ctx : EvalContext) {term : Comp} :
    (ctx.plug term).BaseOnly ↔ term.BaseOnly ∧ EvalContextBaseOnly ctx := by
  induction ctx generalizing term with
  | nil => simp [EvalContextBaseOnly]
  | cons frame rest ih =>
      cases frame with
      | letE body =>
          rw [EvalContext.plug_cons, ih]
          simp only [Frame.plug, Comp.BaseOnly, EvalContextBaseOnly]
          constructor
          · rintro ⟨⟨termOnly, bodyOnly⟩, restOnly⟩
            exact ⟨termOnly, bodyOnly, restOnly⟩
          · rintro ⟨termOnly, bodyOnly, restOnly⟩
            exact ⟨⟨termOnly, bodyOnly⟩, restOnly⟩

theorem EvalContext.plug_baseOnly {ctx : EvalContext} {term : Comp}
    (ctxOnly : EvalContextBaseOnly ctx)
    (termOnly : term.BaseOnly) : (ctx.plug term).BaseOnly :=
  (ctx.plug_baseOnly_iff).mpr ⟨termOnly, ctxOnly⟩

theorem BaseRequest.resume_baseOnly {request : BaseRequest} {response : Val}
    (sourceOnly : request.source.BaseOnly)
    (responseOnly : response.BaseOnly) :
    (request.resume response).BaseOnly := by
  have contextOnly := (request.context.plug_baseOnly_iff.mp sourceOnly).2
  exact request.context.plug_baseOnly contextOnly
    (show (Comp.ret response).BaseOnly from responseOnly)

theorem Comp.baseOnly_head_not_free {term : Comp} (baseOnly : term.BaseOnly) :
    ∀ request : FreeRequest, term.head ≠ .free request := by
  intro request exposed
  have source := Comp.head_free_sound exposed
  rw [source] at baseOnly
  exact request.context.plug_not_baseOnly (by simp [Comp.BaseOnly]) baseOnly

inductive Steps : Comp → Comp → Type where
  | refl : Steps term term
  | step : Step term middle → Steps middle result → Steps term result

theorem Steps.preservesBaseOnly (steps : Steps term result)
    (baseOnly : term.BaseOnly) : result.BaseOnly := by
  induction steps with
  | refl => exact baseOnly
  | step first rest ih => exact ih (first.preservesBaseOnly baseOnly)

/-- Full finite operational conservativity: no sequence of internal steps
from an old-language term can expose a user-defined free request. -/
theorem Steps.baseOnly_never_exposes_free (steps : Steps term result)
    (baseOnly : term.BaseOnly) (request : FreeRequest) :
    result.head ≠ .free request :=
  Comp.baseOnly_head_not_free (steps.preservesBaseOnly baseOnly) request

end EffectSemantics
