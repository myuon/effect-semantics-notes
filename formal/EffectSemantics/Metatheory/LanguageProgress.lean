import EffectSemantics.Metatheory.LanguagePreservation

namespace EffectSemantics

/-- An unhandled operation together with the surrounding CBV `let` stack. -/
inductive LanguageBoundary {mode : RecMode} : LanguageComp mode → Type where
  | base : LanguageBoundary (.baseOp operation parameter)
  | free : LanguageBoundary (.freeOp interface operation parameter)
  | underLet : LanguageBoundary bound →
      LanguageBoundary (.letE bound body)

inductive LanguageProgress {mode : RecMode} : LanguageComp mode → Type where
  | returned : LanguageProgress (.ret value)
  | internal : term ⟶ term' → LanguageProgress term
  | boundary : LanguageBoundary term → LanguageProgress term

/-- The three progress classes are mutually exclusive.  This is the missing
"selected position" half of unique decomposition; uniqueness of the reduct
inside the `internal` class is supplied by `LanguageStep.deterministic`. -/
theorem LanguageBoundary.not_return
    (boundary : LanguageBoundary (.ret value)) : False := by
  cases boundary

theorem LanguageStep.not_boundary
    (step : term ⟶ next) : LanguageBoundary term → False := by
  intro boundary
  induction step with
  | letReturn =>
      cases boundary with
      | underLet inner => exact inner.not_return
  | beta => cases boundary
  | fixBeta => cases boundary
  | ifTrue => cases boundary
  | ifFalse => cases boundary
  | caseInl => cases boundary
  | caseInr => cases boundary
  | underLet _ ih =>
      cases boundary with
      | underLet inner => exact ih inner

inductive LanguageProgressKind where
  | returned
  | internal
  | boundary
  deriving DecidableEq

def LanguageProgress.kind : LanguageProgress term → LanguageProgressKind
  | .returned => .returned
  | .internal _ => .internal
  | .boundary _ => .boundary

/-- Any two progress derivations for the same closed term select the same
outer class.  Together with `LanguageStep.deterministic`, an internal class
also selects a unique reduct. -/
theorem LanguageProgress.kind_unique
    (first second : LanguageProgress term) : first.kind = second.kind := by
  cases first with
  | returned =>
      cases second with
      | returned => rfl
      | internal step => cases step
      | boundary request => exact False.elim request.not_return
  | internal firstStep =>
      cases second with
      | returned => cases firstStep
      | internal _ => rfl
      | boundary request => exact False.elim (firstStep.not_boundary request)
  | boundary firstRequest =>
      cases second with
      | returned => cases firstRequest
      | internal secondStep => exact False.elim (secondStep.not_boundary firstRequest)
      | boundary _ => rfl

/-- The two externally exposed boundary classes used by Chapter II. -/
inductive LanguageBoundaryKind where
  | base
  | free
  deriving DecidableEq

def LanguageBoundary.kind : LanguageBoundary term → LanguageBoundaryKind
  | .base => .base
  | .free => .free
  | .underLet inner => inner.kind

theorem LanguageBoundary.kind_unique
    (first second : LanguageBoundary term) : first.kind = second.kind := by
  induction first with
  | base => cases second <;> rfl
  | free => cases second <;> rfl
  | underLet _ ih =>
      cases second with
      | underLet inner => exact ih inner

/-- The four-way progress classification stated in Chapter II. -/
inductive LanguageDetailedProgressKind where
  | returned
  | internal
  | base
  | free
  deriving DecidableEq

def LanguageProgress.detailedKind (progress : LanguageProgress term) :
    LanguageDetailedProgressKind :=
  match progress with
  | .returned => .returned
  | .internal _ => .internal
  | .boundary request =>
    match request.kind with
    | .base => .base
    | .free => .free

theorem LanguageProgress.detailedKind_unique
    (first second : LanguageProgress term) :
    first.detailedKind = second.detailedKind := by
  cases first with
  | returned =>
      cases second with
      | returned => rfl
      | internal step => cases step
      | boundary boundary => exact False.elim boundary.not_return
  | internal firstStep =>
      cases second with
      | returned => cases firstStep
      | internal _ => rfl
      | boundary boundary => exact False.elim (firstStep.not_boundary boundary)
  | boundary firstBoundary =>
      cases second with
      | returned => exact False.elim firstBoundary.not_return
      | internal step => exact False.elim (step.not_boundary firstBoundary)
      | boundary secondBoundary =>
          have same := firstBoundary.kind_unique secondBoundary
          simpa [LanguageProgress.detailedKind] using congrArg
            (fun kind => match kind with
              | .base => LanguageDetailedProgressKind.base
              | .free => LanguageDetailedProgressKind.free)
            same

/-- Canonical forms for closed Boolean values. -/
theorem HasLanguageVal.closed_bool_canonical
    (typing : [] ⊢[sig] value :ᵥ .bool) :
    ∃ boolean, value = .bool boolean := by
  cases typing with
  | var lookup => nomatch lookup
  | bool => exact ⟨_, rfl⟩

/-- Canonical forms for closed function values, including recursive
functions. -/
theorem HasLanguageVal.closed_arr_canonical
    (typing : [] ⊢[sig] value :ᵥ .arr domain latent codomain) :
    (∃ body, value = .lam domain latent body) ∨
      (∃ allowed body, value = .fixLam allowed domain latent body) := by
  cases typing with
  | var lookup => nomatch lookup
  | lam => exact Or.inl ⟨_, rfl⟩
  | fixLam => exact Or.inr ⟨_, _, rfl⟩

/-- Canonical forms for closed sum values. -/
theorem HasLanguageVal.closed_sum_canonical
    (typing : [] ⊢[sig] value :ᵥ .sum leftTy rightTy) :
    (∃ left, value = .inl left rightTy) ∨
      (∃ right, value = .inr leftTy right) := by
  cases typing with
  | var lookup => nomatch lookup
  | inl => exact Or.inl ⟨_, rfl⟩
  | inr => exact Or.inr ⟨_, rfl⟩

/-- Closed, well-typed language-graded computations return, reduce, or expose
one base/free boundary. -/
def HasLanguageComp.progressClosed
    (typing : [] ⊢[sig] term : ty ! effect) :
    LanguageProgress term :=
  match typing with
  | .subeffect inner _ => inner.progressClosed
  | .ret _ => .returned
  | .baseOp _ _ => .boundary .base
  | .freeOp _ _ => .boundary .free
  | .letE boundTyping _ =>
      match boundTyping.progressClosed with
      | .returned => .internal .letReturn
      | .internal step => .internal (.underLet step)
      | .boundary request => .boundary (.underLet request)
  | .app functionTyping _ =>
      match functionTyping with
      | .var lookup => nomatch lookup
      | .lam _ => .internal .beta
      | .fixLam _ _ => .internal .fixBeta
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

/-- Exactly one input satisfies a predicate. -/
def ExactlyOne (predicate : α → Prop) : Prop :=
  ∃ witness, predicate witness ∧
    ∀ other, predicate other → other = witness

/-- The proposition represented by each of the four Chapter-II progress
classes. -/
def LanguageDetailedProgressCase {mode : RecMode} (term : LanguageComp mode) :
    LanguageDetailedProgressKind → Prop
  | .returned => ∃ value, term = .ret value
  | .internal => ∃ next, Nonempty (term ⟶ next)
  | .base => ∃ boundary : LanguageBoundary term, boundary.kind = .base
  | .free => ∃ boundary : LanguageBoundary term, boundary.kind = .free

theorem LanguageProgress.toDetailedCase (progress : LanguageProgress term) :
    LanguageDetailedProgressCase term progress.detailedKind := by
  cases progress with
  | returned =>
      change ∃ value, LanguageComp.ret _ = .ret value
      exact ⟨_, rfl⟩
  | internal step =>
      simp only [LanguageProgress.detailedKind, LanguageDetailedProgressCase]
      exact ⟨_, ⟨step⟩⟩
  | boundary boundary =>
      cases kindEq : boundary.kind with
      | base =>
          simp only [LanguageProgress.detailedKind, kindEq,
            LanguageDetailedProgressCase]
          exact ⟨boundary, kindEq⟩
      | free =>
          simp only [LanguageProgress.detailedKind, kindEq,
            LanguageDetailedProgressCase]
          exact ⟨boundary, kindEq⟩

/-- The research-note Chapter-II statement directly: exactly one of return,
internal reduction, exposed base request, or exposed free request applies. -/
theorem HasLanguageComp.progressClosed_fourWayExactlyOne
    (typing : [] ⊢[sig] term : ty ! effect) :
    ExactlyOne (LanguageDetailedProgressCase term) := by
  have progress := typing.progressClosed
  refine ⟨progress.detailedKind, progress.toDetailedCase, ?_⟩
  intro kind case
  cases progress with
  | returned =>
      cases kind with
      | returned => simp [LanguageProgress.detailedKind]
      | internal => obtain ⟨_, ⟨step⟩⟩ := case; cases step
      | base => obtain ⟨boundary, _⟩ := case; exact False.elim boundary.not_return
      | free => obtain ⟨boundary, _⟩ := case; exact False.elim boundary.not_return
  | internal progressStep =>
      cases kind with
      | returned => obtain ⟨_, same⟩ := case; subst term; cases progressStep
      | internal => simp [LanguageProgress.detailedKind]
      | base =>
          obtain ⟨boundary, _⟩ := case
          exact False.elim (progressStep.not_boundary boundary)
      | free =>
          obtain ⟨boundary, _⟩ := case
          exact False.elim (progressStep.not_boundary boundary)
  | boundary progressBoundary =>
      cases kind with
      | returned =>
          obtain ⟨_, same⟩ := case
          subst term
          exact False.elim progressBoundary.not_return
      | internal =>
          obtain ⟨_, ⟨step⟩⟩ := case
          exact False.elim (step.not_boundary progressBoundary)
      | base =>
          obtain ⟨boundary, boundaryKind⟩ := case
          have progressKind : progressBoundary.kind = .base :=
            (boundary.kind_unique progressBoundary).symm.trans boundaryKind
          simp [LanguageProgress.detailedKind, progressKind]
      | free =>
          obtain ⟨boundary, boundaryKind⟩ := case
          have progressKind : progressBoundary.kind = .free :=
            (boundary.kind_unique progressBoundary).symm.trans boundaryKind
          simp [LanguageProgress.detailedKind, progressKind]

/-- The proposition represented by each of the three progress classes. -/
def LanguageProgressCase {mode : RecMode} (term : LanguageComp mode) :
    LanguageProgressKind → Prop
  | .returned => ∃ value, term = .ret value
  | .internal => ∃ next, Nonempty (term ⟶ next)
  | .boundary => Nonempty (LanguageBoundary term)

/-- Every progress derivation witnesses its corresponding proposition. -/
theorem LanguageProgress.toCase (progress : LanguageProgress term) :
    LanguageProgressCase term progress.kind := by
  cases progress with
  | returned => exact ⟨_, rfl⟩
  | internal step => exact ⟨_, ⟨step⟩⟩
  | boundary boundary => exact ⟨boundary⟩

/-- The concise form of the research-note progress theorem: exactly one of
the returned, internal-step, or exposed-boundary classes applies. -/
theorem HasLanguageComp.progressClosed_exactlyOne
    (typing : [] ⊢[sig] term : ty ! effect) :
    ExactlyOne (LanguageProgressCase term) := by
  have progress := typing.progressClosed
  refine ⟨progress.kind, progress.toCase, ?_⟩
  intro kind case
  cases progress with
  | returned =>
      cases kind with
      | returned => rfl
      | internal =>
          obtain ⟨next, ⟨step⟩⟩ := case
          cases step
      | boundary =>
          obtain ⟨boundary⟩ := case
          exact False.elim boundary.not_return
  | internal progressStep =>
      cases kind with
      | returned =>
          obtain ⟨value, same⟩ := case
          cases same
          cases progressStep
      | internal => rfl
      | boundary =>
          obtain ⟨boundary⟩ := case
          exact False.elim (progressStep.not_boundary boundary)
  | boundary progressBoundary =>
      cases kind with
      | returned =>
          obtain ⟨value, same⟩ := case
          cases same
          exact False.elim progressBoundary.not_return
      | internal =>
          obtain ⟨next, ⟨step⟩⟩ := case
          exact False.elim (step.not_boundary progressBoundary)
      | boundary => rfl

/-- The exact progress theorem with all three alternatives and their pairwise
exclusivity expanded. -/
theorem HasLanguageComp.progressClosed_cases
    (typing : [] ⊢[sig] term : ty ! effect) :
    ((∃ value, term = .ret value) ∨
      (∃ next, Nonempty (term ⟶ next)) ∨
      Nonempty (LanguageBoundary term)) ∧
    ¬ ((∃ value, term = .ret value) ∧
      (∃ next, Nonempty (term ⟶ next))) ∧
    ¬ ((∃ value, term = .ret value) ∧
      Nonempty (LanguageBoundary term)) ∧
    ¬ ((∃ next, Nonempty (term ⟶ next)) ∧
      Nonempty (LanguageBoundary term)) := by
  have progress := typing.progressClosed
  constructor
  · cases progress with
    | returned => exact .inl ⟨_, rfl⟩
    | internal step => exact .inr (.inl ⟨_, ⟨step⟩⟩)
    | boundary boundary => exact .inr (.inr ⟨boundary⟩)
  constructor
  · rintro ⟨⟨value, rfl⟩, ⟨next, ⟨step⟩⟩⟩
    have impossible := LanguageProgress.kind_unique
      (LanguageProgress.returned (value := value))
      (LanguageProgress.internal step)
    contradiction
  constructor
  · rintro ⟨⟨value, rfl⟩, ⟨boundary⟩⟩
    have impossible := LanguageProgress.kind_unique
      (LanguageProgress.returned (value := value))
      (LanguageProgress.boundary boundary)
    contradiction
  · rintro ⟨⟨next, ⟨step⟩⟩, ⟨boundary⟩⟩
    have impossible := LanguageProgress.kind_unique
      (LanguageProgress.internal step)
      (LanguageProgress.boundary boundary)
    contradiction

end EffectSemantics
