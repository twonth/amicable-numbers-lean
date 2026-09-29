import ManuscriptArithmetic
import AnalyticInputs
import GeometricBounds
import Mathlib.Analysis.PSeries

namespace AmicableSigmaBounds
open AmicableManuscript
open scoped BigOperators

theorem primePowerRatio (p e : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.range (e + 1), (p : ℝ) ^ i) / (p : ℝ) ^ e ≤
      (1 - (1 : ℝ) / p)⁻¹ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hden : 0 < 1 - (1 : ℝ) / p := by
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpR
    simp only [one_div_one, one_div] at hh
    simpa only [one_div, inv_one] using sub_pos.mpr hh
  apply (div_le_iff₀ (pow_pos (by linarith) e)).mpr
  rw [mul_comm ((1 - (1 : ℝ) / p)⁻¹), ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  have hh := geom_sum_mul (p : ℝ) (e + 1)
  rw [pow_succ] at hh
  have heq : (∑ i ∈ Finset.range (e + 1), (p : ℝ) ^ i) * (1 - 1 / (p : ℝ)) =
      (p : ℝ) ^ e - 1 / p := by
    field_simp
    nlinarith
  rw [heq]
  linarith [one_div_nonneg.mpr (show (0 : ℝ) ≤ p by positivity)]

theorem sigmaRatioEuler {n : ℕ} (hn : 0 < n) :
    (sigma n : ℝ) / n ≤ ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    have hh := Nat.prod_factorization_pow_eq_self hn.ne'
    simpa [Finsupp.prod, Nat.support_factorization] using (congrArg (fun n : ℕ => (n : ℝ)) hh).symm
  have hsprod : (sigma n : ℝ) = ∏ p ∈ n.primeFactors,
      ∑ i ∈ Finset.range (n.factorization p + 1), (p : ℝ) ^ i := by
    simp only [sigma, ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne',
      mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow]
  rw [hsprod, hnprod, ← Finset.prod_div_distrib]
  exact Finset.prod_le_prod₀ (by intros; positivity)
    (fun p hp => primePowerRatio p _ (Nat.prime_of_mem_primeFactors hp).two_le)

theorem primeFactorCard {n : ℕ} (hn : 0 < n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have hh : 2 ^ n.primeFactors.card ≤ n := calc
    _ = ∏ _ ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hhR : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast hh
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n.primeFactors.card) hhR
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog

theorem primeFactorReciprocals : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ Real.log (n : ℝ) →
    ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ Real.log (Real.log (Real.log n)) + C := by
  classical
  obtain ⟨C, hC⟩ := AmicableAnalytic.finiteMertens
  refine ⟨C + 1 / Real.log 2, ?_⟩
  intro n hn
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := by omega
    norm_num [heq] at hn
  let P := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Real.log n)
  let Q := n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.log n)
  have hsmall := hC (Real.log n) P hn (by
    intro p hp
    obtain ⟨hp, hple⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, hple⟩)
  have hlarge : ∑ p ∈ Q, (1 : ℝ) / p ≤ 1 / Real.log 2 := by
    calc
      _ ≤ ∑ _ ∈ Q, (1 : ℝ) / Real.log n := Finset.sum_le_sum (by
        intro p hp
        exact one_div_le_one_div_of_le (by linarith) (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2)))
      _ = (Q.card : ℝ) / Real.log n := by simp [div_eq_mul_inv]
      _ ≤ (n.primeFactors.card : ℝ) / Real.log n := div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (by linarith)
      _ ≤ (Real.log n / Real.log 2) / Real.log n :=
        div_le_div_of_nonneg_right (primeFactorCard hnpos) (by linarith)
      _ = _ := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not n.primeFactors
    (fun p : ℕ => (p : ℝ) ≤ Real.log n) (fun p => (1 : ℝ) / p)
  dsimp [P, Q] at hsmall hlarge
  linarith

#print axioms primePowerRatio
#print axioms sigmaRatioEuler
#print axioms primeFactorCard
#print axioms primeFactorReciprocals
end AmicableSigmaBounds


namespace AmicableSigmaBounds
open AmicableManuscript

theorem primeReciprocalSquares (P : Finset ℕ) :
    ∑ p ∈ P, ((1 : ℝ) / p) ^ 2 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ)) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have heq : ∀ n : ℕ, ((1 : ℝ) / n) ^ 2 = (n : ℝ) ^ (-(2 : ℝ)) := by
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]
    simp [one_div, inv_pow]
  simp_rw [heq]
  exact hsum.sum_le_tsum P (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem sigmaLogLogLarge : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ Real.log (n : ℝ) →
    (sigma n : ℝ) ≤ C * n * Real.log (Real.log n) := by
  obtain ⟨C, hC⟩ := primeFactorReciprocals
  let T := ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))
  refine ⟨Real.exp (C + 2 * T), Real.exp_pos _, ?_⟩
  intro n hn
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := by omega
    norm_num [heq] at hn
  have hh := AmicableGeometric.finiteGeometricBound n.primeFactors (fun p : ℕ => (1 : ℝ) / p)
    (1 / 2) (Real.log (Real.log (Real.log n)) + C) T (by norm_num) (by
      intro p hp
      constructor
      · positivity
      · exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le))
    (hC n hn) (primeReciprocalSquares _)
  have hbound := (sigmaRatioEuler hnpos).trans hh
  have heq : Real.exp (Real.log (Real.log (Real.log n)) + C + T / (1 - 1 / 2)) =
      Real.exp (C + 2 * T) * Real.log (Real.log n) := by
    rw [show Real.log (Real.log (Real.log n)) + C + T / (1 - 1 / 2) =
      (C + 2 * T) + Real.log (Real.log (Real.log n)) by ring, Real.exp_add,
      Real.exp_log (Real.log_pos (by linarith))]
  rw [heq] at hbound
  have hh' := (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).mp hbound
  nlinarith

theorem sigmaLogLog : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    (sigma n : ℝ) ≤ C * n * Real.log (Real.log (3 * n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := sigmaLogLogLarge
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    simpa only [Real.log_exp] using hh
  have hll3 : 0 < Real.log (Real.log (3 : ℝ)) := Real.log_pos hlog3
  let D := C + Real.exp 2 / Real.log (Real.log (3 : ℝ))
  have hCD : C ≤ D := by
    dsimp [D]
    linarith [div_pos (Real.exp_pos (2 : ℝ)) hll3]
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  refine ⟨D, hD, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [sigma]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
  have hnpos : (0 : ℝ) < n := by linarith
  have hll : Real.log (Real.log (3 : ℝ)) ≤ Real.log (Real.log (3 * n : ℝ)) := by
    apply Real.log_le_log (by linarith)
    exact Real.log_le_log (by norm_num) (by linarith)
  by_cases hn : 2 ≤ Real.log (n : ℝ)
  · have hmono : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (3 * n : ℝ)) := by
      apply Real.log_le_log (by linarith)
      exact Real.log_le_log hnpos (by linarith)
    exact (hbound n hn).trans (mul_le_mul (mul_le_mul_of_nonneg_right hCD hnpos.le)
      hmono (Real.log_pos (by linarith)).le (by positivity))
  · have hnexp : (n : ℝ) ≤ Real.exp 2 := by
      rw [← Real.exp_log hnpos]
      exact Real.exp_le_exp.mpr (le_of_not_ge hn)
    have hcrude : (sigma n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
    have hDlog : Real.exp 2 ≤ D * Real.log (Real.log (3 : ℝ)) := by
      dsimp [D]
      field_simp
      nlinarith
    calc
      _ ≤ (n : ℝ) ^ 2 := hcrude
      _ ≤ n * Real.exp 2 := by nlinarith
      _ ≤ n * (D * Real.log (Real.log (3 : ℝ))) := mul_le_mul_of_nonneg_left hDlog hnpos.le
      _ ≤ D * n * Real.log (Real.log (3 * n : ℝ)) := by
        simpa only [mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_left hll (mul_nonneg hnpos.le hD.le)

#print axioms primeReciprocalSquares
#print axioms sigmaLogLogLarge
#print axioms sigmaLogLog
end AmicableSigmaBounds

