import Std

/-! Finite logical/counting ingredients. No analytic counting theorem is assumed. -/
namespace AmicableAudit

def sumFirst (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumFirst f n + f n

theorem sumFirstMonotone (f g : Nat → Rat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ g i) : sumFirst f n ≤ sumFirst g n := by
  induction n with
  | zero => simp [sumFirst]
  | succ n ih =>
    have hprev := ih (fun i hi => h i (by omega))
    have hlast := h n (by omega)
    simp only [sumFirst]
    grind

theorem sumFirstStrict (f g : Nat → Rat) (n : Nat) (hn : 0 < n)
    (h : ∀ i, i < n → f i < g i) : sumFirst f n < sumFirst g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hprev := sumFirstMonotone f g k (fun i hi => by have := h i (by omega); grind)
  have hlast := h k (by omega)
  simp only [sumFirst]
  grind

theorem sumFirstScale (f : Nat → Rat) (c : Rat) (n : Nat) :
    sumFirst (fun i => c * f i) n = c * sumFirst f n := by
  induction n with
  | zero => simp [sumFirst]
  | succ n ih => simp only [sumFirst]; grind

/-- The finite averaging principle used to choose V_i,d_i in Case II. -/
theorem weightedSelection (cost weight : Nat → Rat) (c : Rat) (n : Nat)
    (hn : 0 < n) (h : sumFirst cost n ≤ c * sumFirst weight n) :
    ∃ i, i < n ∧ cost i ≤ c * weight i := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hall : ∀ i, i < n → c * weight i < cost i := by grind
  have hstrict := sumFirstStrict (fun i => c * weight i) cost n hn hall
  rw [sumFirstScale] at hstrict
  grind

/-- Why specifying either member of an amicable pair determines the other,
and why exceptional integers also bound the number of exceptional pairs. -/
theorem injectiveOnInvolutiveDomain {α : Type} (f : α → α) (P : α → Prop)
    (h : ∀ x, P x → f (f x) = x)
    (x y : α) (hx : P x) (hy : P y) (hxy : f x = f y) : x = y := by
  have hxx := h x hx
  have hyy := h y hy
  grind

#print axioms sumFirstMonotone
#print axioms sumFirstStrict
#print axioms sumFirstScale
#print axioms weightedSelection
#print axioms injectiveOnInvolutiveDomain

end AmicableAudit
