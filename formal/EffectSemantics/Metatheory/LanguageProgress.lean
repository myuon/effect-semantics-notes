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

end EffectSemantics
