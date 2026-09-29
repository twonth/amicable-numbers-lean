import RoughParts
import DivisorAllocation

namespace AmicableCases
open AmicableManuscript AmicableWeight

structure CommonDivisorData (y : ℝ) (a b B r g : ℕ) : Prop where
  rpos : 0 < r
  gpos : 0 < g
  product : g * r = roughPart y (sigma b)
  dividesA : r ∣ sigma a
  dividesB : r ∣ sigma b
  gbound : g ≤ sigma B
  primes : ∀ p ∈ r.primeFactors, y < (p : ℝ)
  omega : ArithmeticFunction.cardFactors r ≤ roughOmega y (sigma b)

theorem commonDivisorExists (y : ℝ) {a b B : ℕ} (hb : 0 < b) (hB : 0 < B)
    (hdiv : sigma b ∣ sigma B * sigma a) : ∃ r g : ℕ, CommonDivisorData y a b B r g := by
  let v := roughPart y (sigma b)
  let g := Nat.gcd v (sigma B)
  let r := v / g
  have hv : 0 < v := roughPart_pos _ _
  have hsB : 0 < sigma B := by rw [sigma_eq_s_add_self]; omega
  have hsb : 0 < sigma b := by rw [sigma_eq_s_add_self]; omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hv
  have hgv : g ∣ v := Nat.gcd_dvd_left _ _
  have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hv hgv) hg
  have hrv : r ∣ v := Nat.div_dvd_of_dvd hgv
  have hvb : v ∣ sigma b := roughPart_dvd _ hsb.ne'
  refine ⟨r, g, hr, hg, Nat.mul_div_cancel' hgv,
    AmicableAllocation.quotientGcdDivides hv (hvb.trans hdiv), hrv.trans hvb,
    Nat.gcd_le_right _ hsB, ?_, ?_⟩
  · intro p hp
    exact roughPart_primes y (sigma b) (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hrv)
  · have hh := omegaDivisor hv.ne' hrv
    simpa only [v, omegaRoughPart] using hh

theorem commonDivisorCost {y t : ℝ} {a b B r g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) (ht : 0 ≤ t)
    (h : CommonDivisorData y a b B r g) :
    Real.log ((a : ℝ) / r) + t * (ArithmeticFunction.cardFactors r : ℝ) ≤
      Real.log ((a : ℝ) / b) + Real.log (sigma B : ℝ) +
        Real.log (smallPart y (sigma b) : ℝ) + t * (roughOmega y (sigma b) : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hrR : 0 < (r : ℝ) := by exact_mod_cast h.rpos
  have hgR : 0 < (g : ℝ) := by exact_mod_cast h.gpos
  have hspos : 0 < sigma b := by rw [sigma_eq_s_add_self]; omega
  have hsmall : 0 < (smallPart y (sigma b) : ℝ) := by exact_mod_cast smallPart_pos y (sigma b)
  have heq : (sigma b : ℝ) = (smallPart y (sigma b) : ℝ) * ((g : ℝ) * r) := by
    have hh := small_mul_rough y hspos.ne'
    rw [← h.product] at hh
    exact_mod_cast hh.symm
  have hlogeq : Real.log (sigma b : ℝ) = Real.log (smallPart y (sigma b) : ℝ) +
      Real.log (g : ℝ) + Real.log (r : ℝ) := by
    rw [heq, Real.log_mul hsmall.ne' (mul_pos hgR hrR).ne', Real.log_mul hgR.ne' hrR.ne']
    ring
  have hlogb : Real.log (b : ℝ) ≤ Real.log (sigma b : ℝ) := by
    apply Real.log_le_log hbR
    exact_mod_cast (show b ≤ sigma b by rw [sigma_eq_s_add_self]; omega)
  have hlogg := Real.log_le_log hgR (show (g : ℝ) ≤ sigma B by exact_mod_cast h.gbound)
  have homega := mul_le_mul_of_nonneg_left (show (ArithmeticFunction.cardFactors r : ℝ) ≤ roughOmega y (sigma b)
    by exact_mod_cast h.omega) ht
  rw [Real.log_div haR.ne' hrR.ne', Real.log_div haR.ne' hbR.ne']
  linarith

#print axioms commonDivisorExists
#print axioms commonDivisorCost
end AmicableCases
