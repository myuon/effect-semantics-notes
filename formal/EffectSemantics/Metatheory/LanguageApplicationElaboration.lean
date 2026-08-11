import EffectSemantics.Metatheory.LanguageRequests

namespace EffectSemantics

open EffectLanguage

/-- Elaborate general computation application into the fine-grain CBV core.
The function is evaluated first, then the argument, and core application is
performed only after both have returned values. -/
def LanguageComp.elaborateApplication
    (function argument : LanguageComp mode) : LanguageComp mode :=
  .letE function
    (.letE (argument.rename (· + 1)) (.app (.var 1) (.var 0)))

/-- The derived general-application typing rule (C1-PROOF.2.1). -/
def HasLanguageComp.elaborateApplication
    {mode : RecMode}
    {function argument : LanguageComp mode}
    (functionTyping : ctx ⊢[sig] function :
      (.arr domain latent codomain) ! functionEffect)
    (argumentTyping : ctx ⊢[sig] argument : domain ! argumentEffect) :
    ctx ⊢[sig] function.elaborateApplication argument : codomain !
      seq (seq functionEffect argumentEffect) latent := by
  have shiftedArgument := argumentTyping.rename_preserved
    (LanguageRenPreserves.shift ctx (.arr domain latent codomain))
  have functionValue :
      domain :: .arr domain latent codomain :: ctx ⊢[sig]
        LanguageVal.var (mode := mode) 1 :ᵥ
          .arr domain latent codomain := .var rfl
  have argumentValue :
      domain :: .arr domain latent codomain :: ctx ⊢[sig]
        LanguageVal.var (mode := mode) 0 :ᵥ domain := .var rfl
  have coreApplication :
      domain :: .arr domain latent codomain :: ctx ⊢[sig]
        LanguageComp.app (.var 1) (.var 0) : codomain ! latent :=
    .app functionValue argumentValue
  have elaborated :
      ctx ⊢[sig] function.elaborateApplication argument : codomain !
        seq functionEffect (seq argumentEffect latent) :=
    .letE functionTyping (.letE shiftedArgument coreApplication)
  rw [EffectLanguage.seq_assoc]
  exact elaborated

/-- The argument-evaluation phase after the function has returned. -/
def LanguageComp.applicationArgumentPhase
    (function : LanguageVal .finite) (argument : FinLanguageComp) :
    FinLanguageComp :=
  .letE argument (.app (function.rename (· + 1)) (.var 0))

/-- A function-side step is the selected step of an elaborated application. -/
def LanguageStep.elaborateApplication_function
    (step : function ⟶ function') :
    function.elaborateApplication argument ⟶
      function'.elaborateApplication argument :=
  .underLet step

/-- Returning the function advances to the argument-evaluation phase. -/
def languageElaborateApplication_functionReturn
    (function : FinLanguageVal) (argument : FinLanguageComp) :
    LanguageComp.elaborateApplication (.ret function) argument ⟶
      LanguageComp.applicationArgumentPhase function argument := by
  change LanguageComp.letE (.ret function)
      (.letE (argument.rename (· + 1)) (.app (.var 1) (.var 0))) ⟶ _
  have same :
      (LanguageComp.letE (argument.rename (· + 1))
        (.app (.var 1) (.var 0))).subst0 function =
        LanguageComp.applicationArgumentPhase function argument := by
    simp only [LanguageComp.subst0, LanguageComp.subst,
      LanguageComp.applicationArgumentPhase]
    congr 1
    exact LanguageComp.subst_rename_cancel (· + 1)
      (fun | 0 => function | index + 1 => .var index)
      (fun _ => rfl) argument
  rw [← same]
  exact .letReturn

/-- Once the function has returned, argument-side steps are selected next. -/
def LanguageStep.applicationArgumentPhase_argument
    (step : argument ⟶ argument') :
    LanguageComp.applicationArgumentPhase function argument ⟶
      LanguageComp.applicationArgumentPhase function argument' :=
  .underLet step

/-- Returning the argument exposes the core value application. -/
def languageApplicationArgumentPhase_return
    (function argument : FinLanguageVal) :
    LanguageComp.applicationArgumentPhase function (.ret argument) ⟶
      .app function argument := by
  change LanguageComp.letE (.ret argument)
      (.app (function.rename (· + 1)) (.var 0)) ⟶ _
  have same :
      (LanguageComp.app (function.rename (· + 1)) (.var 0)).subst0 argument =
        .app function argument := by
    simp only [LanguageComp.subst0, LanguageComp.subst, LanguageVal.subst]
    congr 1
    exact LanguageVal.subst_rename_cancel (· + 1)
      (fun | 0 => argument | index + 1 => .var index)
      (fun _ => rfl) function
  rw [← same]
  exact .letReturn

end EffectSemantics
