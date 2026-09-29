import ManuscriptArithmetic
import DivisorAllocation

namespace AmicableSelection
open scoped BigOperators

theorem productCrossing {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (U B : ℝ) (hU : 1 ≤ U) (hB : ∀ i ∈ I, 0 ≤ f i ∧ f i ≤ B)
    (hprod : U < ∏ i ∈ I, f i) :
    ∃ J ⊆ I, U < ∏ i ∈ J, f i ∧ ∏ i ∈ J, f i ≤ U * B := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hprod; linarith
  | @insert i I hi ih =>
    by_cases htail : U < ∏ j ∈ I, f j
    · obtain ⟨J, hJ, hj1, hj2⟩ := ih (fun j hj => hB j (Finset.mem_insert_of_mem hj)) htail
      exact ⟨J, hJ.trans (Finset.subset_insert _ _), hj1, hj2⟩
    · refine ⟨insert i I, Finset.Subset.rfl, hprod, ?_⟩
      rw [Finset.prod_insert hi]
      have hu0 : 0 ≤ U := by linarith
      have hfi := hB i (Finset.mem_insert_self _ _)
      calc
        f i * ∏ j ∈ I, f j ≤ f i * U := mul_le_mul_of_nonneg_left (le_of_not_gt htail) hfi.1
        _ ≤ B * U := mul_le_mul_of_nonneg_right hfi.2 hu0
        _ = U * B := mul_comm _ _

theorem squarefreeDivisorCrossing {a : ℕ} (ha : Squarefree a) {U B : ℝ}
    (hU : 1 ≤ U) (haU : U < (a : ℝ))
    (hprime : ∀ p ∈ a.primeFactors, (p : ℝ) ≤ B) :
    ∃ D : ℕ, D ∣ a ∧ U < (D : ℝ) ∧ (D : ℝ) ≤ U * B := by
  classical
  have hprod : U < ∏ p ∈ a.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ha]
    exact haU
  obtain ⟨J, hJ, hlow, hupp⟩ := productCrossing a.primeFactors (fun p => (p : ℝ)) U B
    hU (fun p hp => ⟨Nat.cast_nonneg _, hprime p hp⟩) hprod
  refine ⟨∏ p ∈ J, p, ?_, ?_, ?_⟩
  · rw [← Nat.prod_primeFactors_of_squarefree ha]
    exact Finset.prod_dvd_prod_of_subset J a.primeFactors (fun p => p) hJ
  · simpa only [Nat.cast_prod] using hlow
  · simpa only [Nat.cast_prod] using hupp

#print axioms productCrossing
#print axioms squarefreeDivisorCrossing
end AmicableSelection

