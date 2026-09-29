import DivisorSelection
import WeightArithmetic

namespace AmicableCases
open AmicableManuscript AmicableWeight
open scoped BigOperators

/-- The lower bound for r_0 in Case I, before the asymptotic substitutions. -/
theorem goodPrimeProduct (I : Finset ℕ) (e : ℕ → ℕ)
    (hI : ∀ q ∈ I, q.Prime) (he : ∀ q ∈ I, 0 < e q) :
    (∏ q ∈ I, (q : ℝ)) / (∏ q ∈ I, (e q : ℝ)) ^ (10 / 9 : ℝ) ≤
      ∏ q ∈ I.filter (fun q => (e q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)), (q : ℝ) := by
  classical
  let J := I.filter (fun q => (e q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ))
  let K := I \ J
  have hK : ∀ q ∈ K, (q : ℝ) ≤ (e q : ℝ) ^ (10 / 9 : ℝ) := by
    intro q hq
    obtain ⟨hqI, hqJ⟩ := Finset.mem_sdiff.mp hq
    have hbad : (q : ℝ) ^ (9 / 10 : ℝ) < (e q : ℝ) := by
      by_contra hh
      exact hqJ (Finset.mem_filter.mpr ⟨hqI, le_of_not_gt hh⟩)
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg q) _) hbad.le (by norm_num : (0 : ℝ) ≤ 10 / 9)
    rw [← Real.rpow_mul (Nat.cast_nonneg q)] at hh
    norm_num at hh
    exact hh
  have hsmall : ∏ q ∈ K, (e q : ℝ) ≤ ∏ q ∈ I, (e q : ℝ) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.sdiff_subset) (fun q _ => Nat.cast_nonneg _)
      (fun q hq _ => by exact_mod_cast he q hq)
  have hbadprod : ∏ q ∈ K, (q : ℝ) ≤ (∏ q ∈ I, (e q : ℝ)) ^ (10 / 9 : ℝ) := by
    calc
      _ ≤ ∏ q ∈ K, (e q : ℝ) ^ (10 / 9 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hK
      _ = (∏ q ∈ K, (e q : ℝ)) ^ (10 / 9 : ℝ) :=
        Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) _
      _ ≤ _ := Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hsmall (by norm_num)
  have hsplit : (∏ q ∈ J, (q : ℝ)) * (∏ q ∈ K, (q : ℝ)) = ∏ q ∈ I, (q : ℝ) := by
    simpa only [mul_comm] using (Finset.prod_sdiff (f := fun q : ℕ => (q : ℝ)) (Finset.filter_subset (fun q => (e q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) I))
  have hden : 0 < (∏ q ∈ I, (e q : ℝ)) ^ (10 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Finset.prod_pos (fun q hq => by exact_mod_cast he q hq)) _
  apply (div_le_iff₀ hden).mpr
  rw [← hsplit]
  exact mul_le_mul_of_nonneg_left hbadprod (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem selectedAllocationProduct (I J : Finset ℕ) (e : ℕ → ℕ)
    (hJ : J ⊆ I) (hgood : ∀ q ∈ J, (e q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) :
    (∏ q ∈ J, (e q : ℝ)) ≤ (∏ q ∈ J, (q : ℝ)) ^ (9 / 10 : ℝ) := by
  calc
    _ ≤ ∏ q ∈ J, (q : ℝ) ^ (9 / 10 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hgood
    _ = _ := Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) _

#print axioms goodPrimeProduct
#print axioms selectedAllocationProduct
end AmicableCases


