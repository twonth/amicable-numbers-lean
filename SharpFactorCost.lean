import GcdCounting
import SigmaReciprocals

namespace AmicableGcdCounting
open AmicableManuscript

/-- The cancellation of log log log in the manuscript's multiplicative-partition count. -/
theorem sharpFactorCost {K C t : ℝ} (hK : 0 ≤ K) (hC : 1 ≤ C) (ht : 0 < t)
    (hKt : K ≤ C * t) (d : ℕ)
    (hJ : (ArithmeticFunction.cardFactors d : ℝ) ≤ Real.exp t / t) :
    factorCost K d ≤ Real.exp ((ArithmeticFunction.cardFactors d : ℝ) * t +
      Real.log (2 * C) * Real.exp t / t) := by
  let J := ArithmeticFunction.cardFactors d
  have hbase : 2 * K * (J : ℝ) ≤ 2 * C * Real.exp t := by
    have h1 := mul_le_mul_of_nonneg_right hKt (show 0 ≤ 2 * (J : ℝ) by positivity)
    have h2 := (le_div_iff₀ ht).mp hJ
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * C by positivity)
    nlinarith
  have hp : (2 * K * (J : ℝ)) ^ J ≤ (2 * C * Real.exp t) ^ J := by
    gcongr
  have hid : (2 * C * Real.exp t) ^ J = Real.exp ((Real.log (2 * C) + t) * J) := by
    rw [mul_comm (Real.log (2 * C) + t), Real.exp_nat_mul, Real.exp_add,
      Real.exp_log (by positivity : 0 < 2 * C)]
  have hlog : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have he : (Real.log (2 * C) + t) * (J : ℝ) ≤
      (J : ℝ) * t + Real.log (2 * C) * Real.exp t / t := by
    have hh := mul_le_mul_of_nonneg_left hJ hlog
    change Real.log (2 * C) * (J : ℝ) ≤ Real.log (2 * C) * (Real.exp t / t) at hh
    rw [← mul_div_assoc] at hh
    nlinarith
  calc
    factorCost K d = (2 * K * (J : ℝ)) ^ J := by simp only [factorCost, J, mul_pow]
    _ ≤ (2 * C * Real.exp t) ^ J := hp
    _ = Real.exp ((Real.log (2 * C) + t) * J) := hid
    _ ≤ _ := Real.exp_le_exp.mpr he

#print axioms sharpFactorCost
end AmicableGcdCounting



