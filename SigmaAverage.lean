import ManuscriptArithmetic

namespace AmicableSigmaAverage
open AmicableManuscript
open scoped BigOperators

theorem sumSigmaBound (Z : ℕ) : ∑ n ∈ Finset.range (Z + 1), sigma n ≤ Z * (Z + 1) := by
  classical
  have heq : ∀ n ∈ Finset.range (Z + 1), sigma n =
      ∑ d ∈ Finset.range (Z + 1), if n ≠ 0 ∧ d ∣ n then d else 0 := by
    intro n hn
    rw [sigma_eq_sum_divisors]
    have hset : n.divisors = (Finset.range (Z + 1)).filter (fun d => n ≠ 0 ∧ d ∣ n) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hd, hn0⟩
        exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd)
          (Finset.mem_range.mp hn), hn0, hd⟩
      · rintro ⟨_, hn0, hd⟩
        exact ⟨hd, hn0⟩
    rw [hset, Finset.sum_filter]
  calc
    _ = ∑ n ∈ Finset.range (Z + 1), ∑ d ∈ Finset.range (Z + 1),
        if n ≠ 0 ∧ d ∣ n then d else 0 := Finset.sum_congr rfl heq
    _ = ∑ d ∈ Finset.range (Z + 1), ∑ n ∈ Finset.range (Z + 1),
        if n ≠ 0 ∧ d ∣ n then d else 0 := Finset.sum_comm
    _ = ∑ d ∈ Finset.range (Z + 1), (Z / d) * d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.card_multiples']
    _ ≤ ∑ d ∈ Finset.range (Z + 1), Z := Finset.sum_le_sum
      (fun d _ => Nat.div_mul_le_self Z d)
    _ = Z * (Z + 1) := by simp [mul_comm]

theorem sumSigmaRealBound (Z : ℕ) :
    ∑ n ∈ Finset.range (Z + 1), (sigma n : ℝ) ≤ (Z : ℝ) * (Z + 1) := by
  exact_mod_cast sumSigmaBound Z

#print axioms sumSigmaBound
#print axioms sumSigmaRealBound
end AmicableSigmaAverage
