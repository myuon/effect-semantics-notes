import EffectSemantics.Metatheory.LanguageProgress

namespace EffectSemantics

mutual
  theorem LanguageVal.rename_rename (value : LanguageVal mode)
      (first second : Nat → Nat) :
      (value.rename first).rename second =
        value.rename (fun index => second (first index)) := by
    cases value with
    | var index => rfl
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.rename, LanguageVal.rename_rename]
    | inl value rightTy =>
        simp [LanguageVal.rename, LanguageVal.rename_rename]
    | inr leftTy value =>
        simp [LanguageVal.rename, LanguageVal.rename_rename]
    | lam domain latent body =>
        change LanguageVal.lam domain latent
            ((body.rename (liftLanguageRen first)).rename (liftLanguageRen second)) =
          LanguageVal.lam domain latent
            (body.rename (liftLanguageRen (fun index => second (first index))))
        rw [LanguageComp.rename_rename]
        apply congrArg (LanguageVal.lam domain latent)
        apply congrArg (body.rename)
        funext index
        cases index <;> rfl
    | fixLam allowed domain latent body =>
        change LanguageVal.fixLam allowed domain latent
            ((body.rename (liftLanguageRen (liftLanguageRen first))).rename
              (liftLanguageRen (liftLanguageRen second))) =
          LanguageVal.fixLam allowed domain latent
            (body.rename (liftLanguageRen
              (liftLanguageRen (fun index => second (first index)))))
        rw [LanguageComp.rename_rename]
        apply congrArg (LanguageVal.fixLam allowed domain latent)
        apply congrArg (body.rename)
        funext index
        cases index with
        | zero => rfl
        | succ index => cases index <;> rfl

  theorem LanguageComp.rename_rename (term : LanguageComp mode)
      (first second : Nat → Nat) :
      (term.rename first).rename second =
        term.rename (fun index => second (first index)) := by
    cases term with
    | ret value =>
        simp [LanguageComp.rename, LanguageVal.rename_rename]
    | letE bound body =>
        change LanguageComp.letE
            ((bound.rename first).rename second)
            ((body.rename (liftLanguageRen first)).rename (liftLanguageRen second)) =
          LanguageComp.letE
            (bound.rename (fun index => second (first index)))
            (body.rename (liftLanguageRen (fun index => second (first index))))
        congr 1
        · exact LanguageComp.rename_rename bound first second
        · rw [LanguageComp.rename_rename]
          apply congrArg (body.rename)
          funext index
          cases index <;> rfl
    | app function argument =>
        simp [LanguageComp.rename, LanguageVal.rename_rename]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.rename, LanguageVal.rename_rename,
          LanguageComp.rename_rename]
    | case scrutinee leftBranch rightBranch =>
        change LanguageComp.case
            ((scrutinee.rename first).rename second)
            ((leftBranch.rename (liftLanguageRen first)).rename (liftLanguageRen second))
            ((rightBranch.rename (liftLanguageRen first)).rename (liftLanguageRen second)) =
          LanguageComp.case
            (scrutinee.rename (fun index => second (first index)))
            (leftBranch.rename (liftLanguageRen (fun index => second (first index))))
            (rightBranch.rename (liftLanguageRen (fun index => second (first index))))
        congr 1
        · exact LanguageVal.rename_rename scrutinee first second
        · rw [LanguageComp.rename_rename]
          apply congrArg (leftBranch.rename)
          funext index
          cases index <;> rfl
        · rw [LanguageComp.rename_rename]
          apply congrArg (rightBranch.rename)
          funext index
          cases index <;> rfl
    | baseOp operation parameter =>
        simp [LanguageComp.rename, LanguageVal.rename_rename]
    | freeOp interface operation parameter =>
        simp [LanguageComp.rename, LanguageVal.rename_rename]
end


mutual
  theorem LanguageVal.rename_subst (value : LanguageVal mode)
      (rename : Nat → Nat) (subst : Nat → LanguageVal mode) :
      (value.rename rename).subst subst =
        value.subst (fun index => subst (rename index)) := by
    cases value with
    | var index => rfl
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.rename_subst]
    | inl value rightTy =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.rename_subst]
    | inr leftTy value =>
        simp [LanguageVal.rename, LanguageVal.subst,
          LanguageVal.rename_subst]
    | lam domain latent body =>
        change LanguageVal.lam domain latent
            ((body.rename (liftLanguageRen rename)).subst (liftLanguageSubst subst)) =
          LanguageVal.lam domain latent
            (body.subst (liftLanguageSubst (fun index => subst (rename index))))
        rw [LanguageComp.rename_subst]
        apply congrArg (LanguageVal.lam domain latent)
        apply congrArg (body.subst)
        funext index
        cases index <;> rfl
    | fixLam allowed domain latent body =>
        change LanguageVal.fixLam allowed domain latent
            ((body.rename (liftLanguageRen (liftLanguageRen rename))).subst
              (liftLanguageSubst (liftLanguageSubst subst))) =
          LanguageVal.fixLam allowed domain latent
            (body.subst (liftLanguageSubst
              (liftLanguageSubst (fun index => subst (rename index)))))
        rw [LanguageComp.rename_subst]
        apply congrArg (LanguageVal.fixLam allowed domain latent)
        apply congrArg (body.subst)
        funext index
        cases index with
        | zero => rfl
        | succ index => cases index <;> rfl

  theorem LanguageComp.rename_subst (term : LanguageComp mode)
      (rename : Nat → Nat) (subst : Nat → LanguageVal mode) :
      (term.rename rename).subst subst =
        term.subst (fun index => subst (rename index)) := by
    cases term with
    | ret value =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.rename_subst]
    | letE bound body =>
        change LanguageComp.letE
            ((bound.rename rename).subst subst)
            ((body.rename (liftLanguageRen rename)).subst (liftLanguageSubst subst)) =
          LanguageComp.letE
            (bound.subst (fun index => subst (rename index)))
            (body.subst (liftLanguageSubst (fun index => subst (rename index))))
        congr 1
        · exact LanguageComp.rename_subst bound rename subst
        · rw [LanguageComp.rename_subst]
          apply congrArg (body.subst)
          funext index
          cases index <;> rfl
    | app function argument =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.rename_subst]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.rename_subst, LanguageComp.rename_subst]
    | case scrutinee leftBranch rightBranch =>
        change LanguageComp.case
            ((scrutinee.rename rename).subst subst)
            ((leftBranch.rename (liftLanguageRen rename)).subst (liftLanguageSubst subst))
            ((rightBranch.rename (liftLanguageRen rename)).subst (liftLanguageSubst subst)) =
          LanguageComp.case
            (scrutinee.subst (fun index => subst (rename index)))
            (leftBranch.subst (liftLanguageSubst (fun index => subst (rename index))))
            (rightBranch.subst (liftLanguageSubst (fun index => subst (rename index))))
        congr 1
        · exact LanguageVal.rename_subst scrutinee rename subst
        · rw [LanguageComp.rename_subst]
          apply congrArg (leftBranch.subst)
          funext index
          cases index <;> rfl
        · rw [LanguageComp.rename_subst]
          apply congrArg (rightBranch.subst)
          funext index
          cases index <;> rfl
    | baseOp operation parameter =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.rename_subst]
    | freeOp interface operation parameter =>
        simp [LanguageComp.rename, LanguageComp.subst,
          LanguageVal.rename_subst]
end

mutual
  theorem LanguageVal.subst_rename (value : LanguageVal mode)
      (subst : Nat → LanguageVal mode) (rename : Nat → Nat) :
      (value.subst subst).rename rename =
        value.subst (fun index => (subst index).rename rename) := by
    cases value with
    | var index => rfl
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.subst, LanguageVal.rename,
          LanguageVal.subst_rename]
    | inl value rightTy =>
        simp [LanguageVal.subst, LanguageVal.rename,
          LanguageVal.subst_rename]
    | inr leftTy value =>
        simp [LanguageVal.subst, LanguageVal.rename,
          LanguageVal.subst_rename]
    | lam domain latent body =>
        simp only [LanguageVal.subst, LanguageVal.rename]
        congr
        rw [LanguageComp.subst_rename]
        apply congrArg (body.subst)
        funext index
        cases index with
        | zero => rfl
        | succ index =>
            simp only [liftLanguageSubst]
            rw [LanguageVal.rename_rename, LanguageVal.rename_rename]
            apply congrArg ((subst index).rename)
            funext inner
            rfl
    | fixLam allowed domain latent body =>
        simp only [LanguageVal.subst, LanguageVal.rename]
        congr
        rw [LanguageComp.subst_rename]
        apply congrArg (body.subst)
        funext index
        cases index with
        | zero => rfl
        | succ index =>
            cases index with
            | zero => rfl
            | succ index =>
                simp only [liftLanguageSubst]
                rw [LanguageVal.rename_rename, LanguageVal.rename_rename,
                  LanguageVal.rename_rename, LanguageVal.rename_rename]
                apply congrArg ((subst index).rename)
                funext inner
                rfl

  theorem LanguageComp.subst_rename (term : LanguageComp mode)
      (subst : Nat → LanguageVal mode) (rename : Nat → Nat) :
      (term.subst subst).rename rename =
        term.subst (fun index => (subst index).rename rename) := by
    cases term with
    | ret value =>
        simp [LanguageComp.subst, LanguageComp.rename,
          LanguageVal.subst_rename]
    | letE bound body =>
        simp only [LanguageComp.subst, LanguageComp.rename]
        congr
        · exact LanguageComp.subst_rename bound subst rename
        · rw [LanguageComp.subst_rename]
          apply congrArg (body.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_rename, LanguageVal.rename_rename]
              apply congrArg ((subst index).rename)
              funext inner
              rfl
    | app function argument =>
        simp [LanguageComp.subst, LanguageComp.rename,
          LanguageVal.subst_rename]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.subst, LanguageComp.rename,
          LanguageVal.subst_rename, LanguageComp.subst_rename]
    | case scrutinee leftBranch rightBranch =>
        simp only [LanguageComp.subst, LanguageComp.rename]
        congr
        · exact LanguageVal.subst_rename scrutinee subst rename
        · rw [LanguageComp.subst_rename]
          apply congrArg (leftBranch.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_rename, LanguageVal.rename_rename]
              apply congrArg ((subst index).rename)
              funext inner
              rfl
        · rw [LanguageComp.subst_rename]
          apply congrArg (rightBranch.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_rename, LanguageVal.rename_rename]
              apply congrArg ((subst index).rename)
              funext inner
              rfl
    | baseOp operation parameter =>
        simp [LanguageComp.subst, LanguageComp.rename,
          LanguageVal.subst_rename]
    | freeOp interface operation parameter =>
        simp [LanguageComp.subst, LanguageComp.rename,
          LanguageVal.subst_rename]
end
mutual
  theorem LanguageVal.subst_subst (value : LanguageVal mode)
      (first second : Nat → LanguageVal mode) :
      (value.subst first).subst second =
        value.subst (fun index => (first index).subst second) := by
    cases value with
    | var index => rfl
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.subst, LanguageVal.subst_subst]
    | inl value rightTy =>
        simp [LanguageVal.subst, LanguageVal.subst_subst]
    | inr leftTy value =>
        simp [LanguageVal.subst, LanguageVal.subst_subst]
    | lam domain latent body =>
        simp only [LanguageVal.subst]
        apply congrArg (LanguageVal.lam domain latent)
        rw [LanguageComp.subst_subst]
        apply congrArg (body.subst)
        funext index
        cases index with
        | zero => rfl
        | succ index =>
            simp only [liftLanguageSubst]
            rw [LanguageVal.rename_subst, LanguageVal.subst_rename]
            rfl
    | fixLam allowed domain latent body =>
        simp only [LanguageVal.subst]
        apply congrArg (LanguageVal.fixLam allowed domain latent)
        rw [LanguageComp.subst_subst]
        apply congrArg (body.subst)
        funext index
        cases index with
        | zero => rfl
        | succ index =>
            cases index with
            | zero => rfl
            | succ index =>
                simp only [liftLanguageSubst]
                rw [LanguageVal.rename_subst, LanguageVal.rename_subst,
                  LanguageVal.subst_rename, LanguageVal.subst_rename]
                rfl

  theorem LanguageComp.subst_subst (term : LanguageComp mode)
      (first second : Nat → LanguageVal mode) :
      (term.subst first).subst second =
        term.subst (fun index => (first index).subst second) := by
    cases term with
    | ret value =>
        simp [LanguageComp.subst, LanguageVal.subst_subst]
    | letE bound body =>
        simp only [LanguageComp.subst]
        congr 1
        · exact LanguageComp.subst_subst bound first second
        · rw [LanguageComp.subst_subst]
          apply congrArg (body.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_subst, LanguageVal.subst_rename]
              rfl
    | app function argument =>
        simp [LanguageComp.subst, LanguageVal.subst_subst]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.subst, LanguageVal.subst_subst,
          LanguageComp.subst_subst]
    | case scrutinee leftBranch rightBranch =>
        simp only [LanguageComp.subst]
        congr 1
        · exact LanguageVal.subst_subst scrutinee first second
        · rw [LanguageComp.subst_subst]
          apply congrArg (leftBranch.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_subst, LanguageVal.subst_rename]
              rfl
        · rw [LanguageComp.subst_subst]
          apply congrArg (rightBranch.subst)
          funext index
          cases index with
          | zero => rfl
          | succ index =>
              simp only [liftLanguageSubst]
              rw [LanguageVal.rename_subst, LanguageVal.subst_rename]
              rfl
    | baseOp operation parameter =>
        simp [LanguageComp.subst, LanguageVal.subst_subst]
    | freeOp interface operation parameter =>
        simp [LanguageComp.subst, LanguageVal.subst_subst]
end

def consLanguageSubst (value : FinLanguageVal)
    (subst : Nat → FinLanguageVal) : Nat → FinLanguageVal
  | 0 => value
  | index + 1 => subst index

theorem LanguageComp.subst_lift_subst0 (term : LanguageComp .finite)
    (subst : Nat → FinLanguageVal) (argument : FinLanguageVal) :
    (term.subst (liftLanguageSubst subst)).subst0 argument =
      term.subst (consLanguageSubst argument subst) := by
  rw [LanguageComp.subst0, LanguageComp.subst_subst]
  apply congrArg (term.subst)
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [liftLanguageSubst]
      exact LanguageVal.subst_rename_cancel (· + 1)
        (fun | 0 => argument | index + 1 => .var index)
        (fun _ => rfl) (subst index)

/-- The converse of internal reduction, in the orientation expected by `Acc`. -/
def LanguageStepRel (next current : FinLanguageComp) : Prop :=
  Nonempty (current ⟶ next)

/-- Strong normalization for the finite language's internal reduction. -/
def LanguageStronglyNormalizing (term : FinLanguageComp) : Prop :=
  Acc LanguageStepRel term

/-- Reflexive-transitive internal reduction. -/
inductive FinLanguageSteps : FinLanguageComp → FinLanguageComp → Type where
  | refl : FinLanguageSteps term term
  | head : term ⟶ next → FinLanguageSteps next result →
      FinLanguageSteps term result

namespace FinLanguageSteps

def single (step : term ⟶ next) : FinLanguageSteps term next :=
  .head step .refl

def trans (first : FinLanguageSteps firstTerm middle)
    (second : FinLanguageSteps middle lastTerm) :
    FinLanguageSteps firstTerm lastTerm :=
  match first with
  | .refl => second
  | .head step rest => .head step (rest.trans second)

end FinLanguageSteps

theorem LanguageStronglyNormalizing.stepBack
    (step : source ⟶ target)
    (targetSN : LanguageStronglyNormalizing target) :
    LanguageStronglyNormalizing source := by
  apply Acc.intro
  intro next nextStep
  obtain ⟨nextStep⟩ := nextStep
  have same := LanguageStep.deterministic nextStep step
  subst next
  exact targetSN

/-- Tait reducibility for finite values.  At function type, a value maps
every reducible argument to a strongly normalizing computation whose returned
values are reducible. -/
def ReducibleLanguageVal : LanguageTy → FinLanguageVal → Prop
  | .unit, value => value = .unit
  | .bool, value => ∃ flag, value = .bool flag
  | .prod leftTy rightTy, value =>
      ∃ left right, value = .pair left right ∧
        ReducibleLanguageVal leftTy left ∧
        ReducibleLanguageVal rightTy right
  | .sum leftTy rightTy, value =>
      (∃ left, value = .inl left rightTy ∧
        ReducibleLanguageVal leftTy left) ∨
      (∃ right, value = .inr leftTy right ∧
        ReducibleLanguageVal rightTy right)
  | .arr domain _ codomain, function =>
      ∀ argument, ReducibleLanguageVal domain argument →
        LanguageStronglyNormalizing (.app function argument) ∧
        ∀ value, FinLanguageSteps (.app function argument) (.ret value) →
          ReducibleLanguageVal codomain value
termination_by ty => sizeOf ty

/-- A reducible computation is strongly normalizing, and every returned
value reachable by internal reduction is reducible at the result type.
Base/free boundaries are permitted terminal forms. -/
def ReducibleLanguageComp (ty : LanguageTy) (term : FinLanguageComp) : Prop :=
  LanguageStronglyNormalizing term ∧
    ∀ value, FinLanguageSteps term (.ret value) →
      ReducibleLanguageVal ty value

def ReducibleLanguageSubst (ctx : LanguageContext)
    (subst : Nat → FinLanguageVal) : Prop :=
  ∀ ⦃index ty⦄, ctx.lookup index = some ty →
    ReducibleLanguageVal ty (subst index)

theorem ReducibleLanguageComp.forward
    (reducible : ReducibleLanguageComp ty source)
    (step : source ⟶ target) : ReducibleLanguageComp ty target := by
  constructor
  · exact Acc.inv reducible.1 ⟨step⟩
  · intro value steps
    exact reducible.2 value (.head step steps)

theorem ReducibleLanguageComp.stepBack
    (step : source ⟶ target)
    (reducible : ReducibleLanguageComp ty target) :
    ReducibleLanguageComp ty source := by
  constructor
  · exact reducible.1.stepBack step
  · intro value steps
    cases steps with
    | refl => cases step
    | head first rest =>
        have same := LanguageStep.deterministic first step
        subst target
        exact reducible.2 value rest

theorem reducibleLanguageRet
    (reducible : ReducibleLanguageVal ty value) :
    ReducibleLanguageComp ty (.ret value) := by
  constructor
  · apply Acc.intro
    intro next step
    obtain ⟨step⟩ := step
    cases step
  · intro result steps
    cases steps with
    | refl => exact reducible
    | head step _ =>
        cases step

theorem reducibleLanguageBaseOp :
    ReducibleLanguageComp ty (.baseOp operation parameter) := by
  constructor
  · apply Acc.intro
    intro next step
    obtain ⟨step⟩ := step
    cases step
  · intro value steps
    cases steps with
    | head step _ =>
        cases step

theorem reducibleLanguageFreeOp :
    ReducibleLanguageComp ty (.freeOp interface operation parameter) := by
  constructor
  · apply Acc.intro
    intro next step
    obtain ⟨step⟩ := step
    cases step
  · intro value steps
    cases steps with
    | head step _ =>
        cases step

def finLanguageSteps_let_to_ret
    (steps : FinLanguageSteps (.letE bound body) (.ret result)) :
    Σ value, FinLanguageSteps bound (.ret value) ×
      FinLanguageSteps (body.subst0 value) (.ret result) :=
  match steps with
  | .head .letReturn rest => ⟨_, .refl, rest⟩
  | .head (.underLet inner) rest =>
      let ⟨value, boundSteps, bodySteps⟩ := finLanguageSteps_let_to_ret rest
      ⟨value, .head inner boundSteps, bodySteps⟩

theorem languageLetStronglyNormalizing
    (boundSN : LanguageStronglyNormalizing bound)
    (bodySN : ∀ value, FinLanguageSteps bound (.ret value) →
      LanguageStronglyNormalizing (body.subst0 value)) :
    LanguageStronglyNormalizing (.letE bound body) := by
  revert body
  induction boundSN with
  | intro bound accessible ih =>
      intro body bodySN
      apply Acc.intro
      intro next step
      obtain ⟨step⟩ := step
      cases step with
      | letReturn => exact bodySN _ .refl
      | underLet inner =>
          exact ih _ ⟨inner⟩ (fun value steps =>
            bodySN value (.head inner steps))

theorem reducibleLanguageLet
    (boundReducible : ReducibleLanguageComp boundTy bound)
    (bodyReducible : ∀ value, ReducibleLanguageVal boundTy value →
      ReducibleLanguageComp resultTy (body.subst0 value)) :
    ReducibleLanguageComp resultTy (.letE bound body) := by
  constructor
  · exact languageLetStronglyNormalizing boundReducible.1
      (fun value steps => (bodyReducible value (boundReducible.2 value steps)).1)
  · intro result steps
    obtain ⟨value, boundSteps, bodySteps⟩ := finLanguageSteps_let_to_ret steps
    exact (bodyReducible value (boundReducible.2 value boundSteps)).2 result bodySteps

theorem ReducibleLanguageSubst.cons
    (reducible : ReducibleLanguageSubst ctx subst)
    (valueReducible : ReducibleLanguageVal ty value) :
    ReducibleLanguageSubst (ty :: ctx) (consLanguageSubst value subst) := by
  intro index found lookup
  cases index with
  | zero =>
      have same : ty = found := Option.some.inj lookup
      subst found
      exact valueReducible
  | succ index => exact reducible lookup

set_option linter.defProp false in
mutual
  /-- Fundamental theorem for finite values under a reducible closing
  substitution. -/
  def HasLanguageVal.reducible
      (typing : ctx ⊢[sig] value :ᵥ ty)
      (substReducible : ReducibleLanguageSubst ctx subst) :
      ReducibleLanguageVal ty (value.subst subst) := by
    cases typing with
    | var lookup => exact substReducible lookup
    | unit => simp [LanguageVal.subst, ReducibleLanguageVal]
    | bool => simp [LanguageVal.subst, ReducibleLanguageVal]
    | pair left right =>
        simp only [LanguageVal.subst, ReducibleLanguageVal]
        exact ⟨_, _, rfl, left.reducible substReducible,
          right.reducible substReducible⟩
    | inl inner =>
        simp only [LanguageVal.subst, ReducibleLanguageVal]
        exact Or.inl ⟨_, rfl, inner.reducible substReducible⟩
    | inr inner =>
        simp only [LanguageVal.subst, ReducibleLanguageVal]
        exact Or.inr ⟨_, rfl, inner.reducible substReducible⟩
    | lam body =>
        simp only [LanguageVal.subst, ReducibleLanguageVal]
        intro argument argumentReducible
        have bodyResult := body.reducible
          (substReducible.cons argumentReducible)
        rw [← LanguageComp.subst_lift_subst0] at bodyResult
        exact bodyResult.stepBack .beta
    | fixLam allowed _ => nomatch allowed
  termination_by (sizeOf value, sizeOf typing)

  /-- Fundamental theorem for finite computations under a reducible closing
  substitution. -/
  def HasLanguageComp.reducible
      (typing : ctx ⊢[sig] term : ty ! effect)
      (substReducible : ReducibleLanguageSubst ctx subst) :
      ReducibleLanguageComp ty (term.subst subst) := by
    cases typing with
    | ret value =>
        exact reducibleLanguageRet (value.reducible substReducible)
    | letE bound body =>
        apply reducibleLanguageLet (bound.reducible substReducible)
        intro value valueReducible
        have bodyResult := body.reducible (substReducible.cons valueReducible)
        rw [← LanguageComp.subst_lift_subst0] at bodyResult
        exact bodyResult
    | app function argument =>
        have functionResult := function.reducible substReducible
        simp only [ReducibleLanguageVal] at functionResult
        exact functionResult _ (argument.reducible substReducible)
    | ite condition thenBranch elseBranch =>
        have conditionResult := condition.reducible substReducible
        simp only [ReducibleLanguageVal] at conditionResult
        obtain ⟨flag, conditionEq⟩ := conditionResult
        simp only [LanguageComp.subst]
        rw [conditionEq]
        cases flag with
        | false =>
            exact (elseBranch.reducible substReducible).stepBack .ifFalse
        | true =>
            exact (thenBranch.reducible substReducible).stepBack .ifTrue
    | case scrutinee leftBranch rightBranch =>
        have scrutineeResult := scrutinee.reducible substReducible
        simp only [ReducibleLanguageVal] at scrutineeResult
        simp only [LanguageComp.subst]
        cases scrutineeResult with
        | inl left =>
            obtain ⟨value, same, valueReducible⟩ := left
            rw [same]
            have branchResult := leftBranch.reducible
              (substReducible.cons valueReducible)
            rw [← LanguageComp.subst_lift_subst0] at branchResult
            exact branchResult.stepBack .caseInl
        | inr right =>
            obtain ⟨value, same, valueReducible⟩ := right
            rw [same]
            have branchResult := rightBranch.reducible
              (substReducible.cons valueReducible)
            rw [← LanguageComp.subst_lift_subst0] at branchResult
            exact branchResult.stepBack .caseInr
    | baseOp lookup parameter => exact reducibleLanguageBaseOp
    | freeOp lookup parameter => exact reducibleLanguageFreeOp
    | subeffect inner bound => exact inner.reducible substReducible
  termination_by (sizeOf term, sizeOf typing)
end

theorem emptyReducibleLanguageSubst :
    ReducibleLanguageSubst [] (fun index => .var index) := by
  intro index ty lookup
  nomatch lookup

theorem liftLanguageSubst_vars {mode : RecMode} :
    liftLanguageSubst (mode := mode)
        (fun index : Nat => LanguageVal.var index) =
      (fun index => LanguageVal.var index) := by
  funext index
  cases index <;> rfl

mutual
  theorem LanguageVal.subst_vars (value : LanguageVal mode) :
      value.subst (fun index => .var index) = value := by
    cases value with
    | var index => rfl
    | unit => rfl
    | bool flag => rfl
    | pair left right =>
        simp [LanguageVal.subst, LanguageVal.subst_vars]
    | inl value rightTy =>
        simp [LanguageVal.subst, LanguageVal.subst_vars]
    | inr leftTy value =>
        simp [LanguageVal.subst, LanguageVal.subst_vars]
    | lam domain latent body =>
        simp only [LanguageVal.subst]
        rw [liftLanguageSubst_vars, LanguageComp.subst_vars]
    | fixLam allowed domain latent body =>
        simp only [LanguageVal.subst]
        rw [liftLanguageSubst_vars, liftLanguageSubst_vars,
          LanguageComp.subst_vars]

  theorem LanguageComp.subst_vars (term : LanguageComp mode) :
      term.subst (fun index => .var index) = term := by
    cases term with
    | ret value => simp [LanguageComp.subst, LanguageVal.subst_vars]
    | letE bound body =>
        simp only [LanguageComp.subst]
        rw [LanguageComp.subst_vars, liftLanguageSubst_vars,
          LanguageComp.subst_vars]
    | app function argument =>
        simp [LanguageComp.subst, LanguageVal.subst_vars]
    | ite condition thenBranch elseBranch =>
        simp [LanguageComp.subst, LanguageVal.subst_vars,
          LanguageComp.subst_vars]
    | case scrutinee leftBranch rightBranch =>
        simp only [LanguageComp.subst]
        rw [LanguageVal.subst_vars, liftLanguageSubst_vars,
          LanguageComp.subst_vars, LanguageComp.subst_vars]
    | baseOp operation parameter =>
        simp [LanguageComp.subst, LanguageVal.subst_vars]
    | freeOp interface operation parameter =>
        simp [LanguageComp.subst, LanguageVal.subst_vars]
end

/-- Every closed, well-typed finite computation is strongly normalizing for
the language's internal reduction relation. -/
theorem HasLanguageComp.stronglyNormalizing
    (typing : @HasLanguageComp sig .finite [] term ty effect) :
    LanguageStronglyNormalizing term := by
  have reducible := typing.reducible emptyReducibleLanguageSubst
  simpa only [LanguageComp.subst_vars] using reducible.1

/-- Every closed, well-typed finite computation reaches either a returned
value or an exposed operation boundary after finitely many internal steps. -/
theorem HasLanguageComp.normalizes
    (typing : @HasLanguageComp sig .finite [] term ty effect) :
    ∃ normal, Nonempty (FinLanguageSteps term normal) ∧
      ((∃ value, normal = .ret value) ∨ Nonempty (LanguageBoundary normal)) := by
  have sn := typing.stronglyNormalizing
  induction sn generalizing ty effect with
  | intro current accessible ih =>
      cases typing.progressClosed with
      | returned =>
          exact ⟨_, ⟨.refl⟩, Or.inl ⟨_, rfl⟩⟩
      | boundary boundary =>
          exact ⟨_, ⟨.refl⟩, Or.inr ⟨boundary⟩⟩
      | internal step =>
          have nextTyping := step.preserve typing
          obtain ⟨normal, ⟨steps⟩, final⟩ :=
            ih _ ⟨step⟩ nextTyping
          exact ⟨normal, ⟨.head step steps⟩, final⟩

end EffectSemantics
