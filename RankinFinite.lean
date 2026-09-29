import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite versions of the first steps of the technical lemma. These avoid any
unproved convergence assertion for the infinite Euler product. -/
namespace AmicableRankin

open scoped BigOperators

theorem squarefreePrimeFactorsInjective (B : Finset ℕ)
    (hB : ∀ b ∈ B, Squarefree b) :
    Set.InjOn Nat.primeFactors (↑B : Set ℕ) := by
  intro a ha b hb hab
  rw [← Nat.prod_primeFactors_of_squarefree (hB a ha),
    ← Nat.prod_primeFactors_of_squarefree (hB b hb), hab]

theorem finiteSquarefreeEulerBound (B P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hB : ∀ b ∈ B, Squarefree b)
    (hP : ∀ b ∈ B, b.primeFactors ⊆ P) :
    ∑ b ∈ B, (∏ p ∈ b.primeFactors, w p) ≤ ∏ p ∈ P, (1 + w p) := by
  classical
  rw [Finset.prod_one_add]
  have heq : ∑ b ∈ B, (∏ p ∈ b.primeFactors, w p) =
      ∑ T ∈ B.image Nat.primeFactors, ∏ p ∈ T, w p := by
    rw [Finset.sum_image]
    exact squarefreePrimeFactorsInjective B hB
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (hP b hb)
  · intro T _ _
    exact Finset.prod_nonneg (fun p _ => hw p)

theorem finiteEulerExpBound (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) :
    ∏ p ∈ P, (1 + w p) ≤ Real.exp (∑ p ∈ P, w p) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p _
    linarith [hw p]
  · intro p _
    linarith [Real.add_one_le_exp (w p)]

/-- Rankin's inequality in precisely the form used before expanding the
squarefree Euler product: every counted b is at most Y and has weight > K. -/
theorem finiteRankin (B : Finset ℕ) (H : ℕ → ℝ)
    (Y K eta delta : ℝ) (hY : 0 < Y) (hK : 0 < K)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hB : ∀ b ∈ B, 0 < b ∧ (b : ℝ) ≤ Y ∧ K < H b) :
    (B.card : ℝ) ≤ Y ^ (1 + delta) * K ^ (-eta) *
      ∑ b ∈ B, (H b) ^ eta / (b : ℝ) ^ (1 + delta) := by
  have hfac : 0 ≤ Y ^ (1 + delta) * K ^ (-eta) := by positivity
  calc
    (B.card : ℝ) = ∑ _b ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ b ∈ B, Y ^ (1 + delta) * K ^ (-eta) *
        ((H b) ^ eta / (b : ℝ) ^ (1 + delta)) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbY, hbH⟩ := hB b hb
      have hbpos' : (0 : ℝ) < b := by exact_mod_cast hbpos
      have hp : (b : ℝ) ^ (1 + delta) ≤ Y ^ (1 + delta) :=
        Real.rpow_le_rpow (le_of_lt hbpos') hbY (by linarith)
      have hq : K ^ eta ≤ (H b) ^ eta :=
        Real.rpow_le_rpow (le_of_lt hK) (le_of_lt hbH) (le_of_lt heta)
      rw [Real.rpow_neg (le_of_lt hK)]
      have hbp : 0 < (b : ℝ) ^ (1 + delta) := Real.rpow_pos_of_pos hbpos' _
      have hkp : 0 < K ^ eta := Real.rpow_pos_of_pos hK _
      have hcross : (b : ℝ) ^ (1 + delta) * K ^ eta ≤
          Y ^ (1 + delta) * (H b) ^ eta :=
        mul_le_mul hp hq (le_of_lt hkp) (by positivity)
      calc
        1 ≤ (Y ^ (1 + delta) * (H b) ^ eta) /
            ((b : ℝ) ^ (1 + delta) * K ^ eta) := by
          apply (le_div_iff₀ (mul_pos hbp hkp)).mpr
          simpa using hcross
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

#print axioms squarefreePrimeFactorsInjective
#print axioms finiteSquarefreeEulerBound
#print axioms finiteEulerExpBound
#print axioms finiteRankin
end AmicableRankin
