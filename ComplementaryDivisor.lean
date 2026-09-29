import GoodPrimeProduct

namespace AmicableCases
open AmicableManuscript AmicableWeight AmicableAllocation
open scoped BigOperators

/-- Removing the factors assigned to R leaves the divisor of sigma(m) used in Case I. -/
theorem complementaryDivisor {a B R g r p : ℕ} (ha : Squarefree a) (hR : R ∣ a)
    (hBA : B.Coprime a) (hg : g ∣ sigma B) (hp : p + 1 = g * r)
    (e : ℕ → ℕ) (he : ∀ q ∈ a.primeFactors, e q ∣ q + 1)
    (heprod : ∏ q ∈ a.primeFactors, e q = r)
    (hgood : ∀ q ∈ R.primeFactors, (e q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) :
    ∃ d : ℕ, d ∣ sigma (B * (a / R)) ∧ d * (∏ q ∈ R.primeFactors, e q) = p + 1 ∧
      (p : ℝ) / (R : ℝ) ^ (9 / 10 : ℝ) < d := by
  classical
  have hRsf := ha.squarefree_of_dvd hR
  have hRp : R.primeFactors ⊆ a.primeFactors := by
    intro q hq
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
      (Nat.dvd_of_mem_primeFactors hq).trans hR, ha.ne_zero⟩
  let K := a.primeFactors \ R.primeFactors
  let d := g * ∏ q ∈ K, e q
  have hprodK : ∏ q ∈ K, q = a / R := by
    simpa only [Nat.prod_primeFactors_of_squarefree hRsf] using
      Nat.prod_primeFactors_sdiff_of_squarefree ha hRp
  have hKpf : (a / R).primeFactors = K := by
    rw [← hprodK]
    exact Nat.primeFactors_prod (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1)
  have hsig : sigma (a / R) = ∏ q ∈ K, (q + 1) := by
    rw [sigma_squarefree (ha.squarefree_of_dvd (Nat.div_dvd_of_dvd hR)), hKpf]
  have hddiv : d ∣ sigma (B * (a / R)) := by
    rw [sigma_mul (hBA.of_dvd_right (Nat.div_dvd_of_dvd hR)), hsig]
    exact mul_dvd_mul hg (Finset.prod_dvd_prod_of_dvd e (fun q => q + 1) (fun q hq => he q (Finset.mem_sdiff.mp hq).1))
  have heq : d * (∏ q ∈ R.primeFactors, e q) = p + 1 := by
    dsimp [d, K]
    rw [mul_assoc, Finset.prod_sdiff hRp, heprod, ← hp]
  have hbound := selectedAllocationProduct a.primeFactors R.primeFactors e hRp hgood
  have hRprod : (∏ q ∈ R.primeFactors, (q : ℝ)) = (R : ℝ) := by
    simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hRsf)
  rw [hRprod] at hbound
  have heqR : (d : ℝ) * (∏ q ∈ R.primeFactors, (e q : ℝ)) = (p : ℝ) + 1 := by exact_mod_cast heq
  have hprod := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg d)
  refine ⟨d, hddiv, heq, ?_⟩
  apply (div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hRsf.ne_zero) _)).mpr
  nlinarith

#print axioms complementaryDivisor
end AmicableCases


