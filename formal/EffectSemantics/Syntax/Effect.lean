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

theorem optional_free (interface : Nat) :
    (1 : Effect) ≤ [EffectAtom.free interface] := nil_le _

theorem insert_free (pre suf : Effect) (interface : Nat) :
    pre * suf ≤ pre * [EffectAtom.free interface] * suf := by
  show (pre ++ suf).Sublist ((pre ++ [EffectAtom.free interface]) ++ suf)
  simp [List.append_assoc]

theorem sublist_nil {e : Effect} (h : e ≤ (1 : Effect)) : e = 1 := by
  exact List.eq_nil_of_sublist_nil h

end Effect
end EffectSemantics
