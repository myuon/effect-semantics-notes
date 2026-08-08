namespace EffectSemantics

/-- Atomic labels in the extended ordered effect algebra.  Base labels and
free interfaces remain nominally distinct. -/
inductive EffectAtom where
  | base (name : Nat)
  | free (interface : Nat)
  deriving DecidableEq, Repr

/-- Exact ordered effect words.  The empty word is the pure effect and append
is sequential composition. -/
abbrev Effect := List EffectAtom

namespace Effect

def pure : Effect := []

def seq (e f : Effect) : Effect := e ++ f

instance : One Effect := ⟨pure⟩
instance : Mul Effect := ⟨seq⟩

@[simp] theorem one_def : (1 : Effect) = [] := rfl
@[simp] theorem mul_def (e f : Effect) : e * f = e ++ f := rfl
@[simp] theorem one_mul (e : Effect) : 1 * e = e := by simp
@[simp] theorem mul_one (e : Effect) : e * 1 = e := by simp
theorem mul_assoc (e f g : Effect) : (e * f) * g = e * (f * g) := by
  simp [List.append_assoc]

/-- `e ≤ f` means that `e` is an ordered subsequence of the upper bound `f`.
It validates optional insertion, but never exchanges existing atoms. -/
def Le (e f : Effect) : Prop := e.Sublist f

instance : LE Effect := ⟨Le⟩

theorem le_refl (e : Effect) : e ≤ e := List.Sublist.refl e

theorem le_trans {e f g : Effect} (hef : e ≤ f) (hfg : f ≤ g) : e ≤ g :=
  hef.trans hfg

theorem nil_le (e : Effect) : (1 : Effect) ≤ e := by
  show ([] : Effect).Sublist e
  exact List.nil_sublist e

theorem le_seq {e e' f f' : Effect} (he : e ≤ e') (hf : f ≤ f') :
    e * f ≤ e' * f' := by
  exact he.append hf

theorem le_seq_left {e e' : Effect} (h : e ≤ e') (f : Effect) :
    e * f ≤ e' * f := le_seq h (le_refl f)

theorem le_seq_right (e : Effect) {f f' : Effect} (h : f ≤ f') :
    e * f ≤ e * f' := le_seq (le_refl e) h

theorem le_left_padding (e f : Effect) : f ≤ e * f := by
  simpa only [one_mul] using le_seq (nil_le e) (le_refl f)

theorem optional_free (interface : Nat) :
    (1 : Effect) ≤ [EffectAtom.free interface] := nil_le _

theorem insert_free (pre suf : Effect) (interface : Nat) :
    pre * suf ≤ pre * [EffectAtom.free interface] * suf := by
  show (pre ++ suf).Sublist ((pre ++ [EffectAtom.free interface]) ++ suf)
  simp [List.append_assoc]

theorem sublist_nil {e : Effect} (h : e ≤ (1 : Effect)) : e = 1 := by
  exact List.eq_nil_of_sublist_nil h

def FreeOf (interface : Nat) (effect : Effect) : Prop :=
  EffectAtom.free interface ∉ effect

theorem factor_not_free {interface : Nat} {suffix effect : Effect}
    (factor : [EffectAtom.free interface] * suffix ≤ effect)
    (freeOf : FreeOf interface effect) : False := by
  apply freeOf
  exact factor.subset (by simp)

/-- No finite ordered word can absorb a mandatory effect occurrence on its
left.  This is the precise obstruction to typing unrestricted effectful
recursion with finite words alone. -/
theorem not_cons_le_self (atom : EffectAtom) (effect : Effect) :
    ¬ ([atom] * effect ≤ effect) := by
  intro absorbed
  have lengthBound := absorbed.length_le
  simp only [mul_def, List.singleton_append, List.length_cons] at lengthBound
  exact Nat.not_succ_le_self effect.length lengthBound

theorem not_free_loop_grade (interface : Nat) (effect : Effect) :
    ¬ ([EffectAtom.free interface] * effect ≤ effect) :=
  not_cons_le_self _ _

/-- If the left prefix contains no selected interface, an embedding of a word
starting with that interface into `prefix ++ interface :: suffix` forces the
remaining source word into `suffix`.  This is the ordered cancellation used by
the sharp shallow-handler theorem. -/
theorem cancel_first_free {interface : Nat} {tail pre suffix : Effect}
    (freeOf : FreeOf interface pre)
    (factor : List.Sublist (EffectAtom.free interface :: tail)
      (pre ++ EffectAtom.free interface :: suffix)) :
    List.Sublist tail suffix := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at factor
      cases factor with
      | cons _ rest => exact List.sublist_of_cons_sublist rest
      | cons_cons _ rest => exact rest
  | cons atom pre ih =>
      simp only [FreeOf, List.mem_cons, not_or] at freeOf
      simp only [List.cons_append] at factor
      cases factor with
      | cons _ rest => exact ih freeOf.2 rest
      | cons_cons _ _ => exact (freeOf.1 rfl).elim

end Effect
end EffectSemantics
