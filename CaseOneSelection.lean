import DivisorSelection
import GoodPrimeProduct

namespace AmicableCases
open scoped BigOperators

theorem caseOneSelectR {r0 p : ℕ} (hsf : Squarefree r0) {U : ℝ}
    (hU : 1 ≤ U) (hr0 : U < (r0 : ℝ))
    (hp : ∀ q ∈ r0.primeFactors, q < p) :
    ∃ R : ℕ, R ∣ r0 ∧ U < (R : ℝ) ∧ ((R.Prime ∧ R < p) ∨ (R : ℝ) ≤ U ^ 2) := by
  classical
  by_cases hlarge : ∃ q ∈ r0.primeFactors, U < (q : ℝ)
  · obtain ⟨q, hq, hqU⟩ := hlarge
    exact ⟨q, Nat.dvd_of_mem_primeFactors hq, hqU,
      Or.inl ⟨Nat.prime_of_mem_primeFactors hq, hp q hq⟩⟩
  · have hsmall : ∀ q ∈ r0.primeFactors, (q : ℝ) ≤ U := by
      intro q hq
      by_contra hh
      exact hlarge ⟨q, hq, lt_of_not_ge hh⟩
    obtain ⟨R, hR, hRU, hRupper⟩ := AmicableSelection.squarefreeDivisorCrossing hsf hU hr0 hsmall
    exact ⟨R, hR, hRU, Or.inr (by simpa [pow_two] using hRupper)⟩

/-- The numerical margin 1 - (4/5)(10/9) > 1/10 used for r_0. -/
theorem goodProductPowerLower {a r r0 x : ℝ} (hx : 1 < x) (hr : 0 < r)
    (hr0 : a / r ^ (10 / 9 : ℝ) ≤ r0)
    (ha : x ^ (199 / 200 : ℝ) ≤ a) (hrx : r ≤ x ^ (161 / 200 : ℝ)) :
    x ^ (1 / 10 : ℝ) < r0 := by
  have hx0 : 0 < x := by linarith
  have hden := Real.rpow_le_rpow hr.le hrx (by norm_num : (0 : ℝ) ≤ 10 / 9)
  have hratio : x ^ (199 / 200 : ℝ) / (x ^ (161 / 200 : ℝ)) ^ (10 / 9 : ℝ) ≤ a / r ^ (10 / 9 : ℝ) := by
    have ha0 : 0 ≤ a := (Real.rpow_nonneg hx0.le (199 / 200 : ℝ)).trans ha
    exact div_le_div₀ ha0 ha (Real.rpow_pos_of_pos hr _) hden
  have hid : x ^ (199 / 200 : ℝ) / (x ^ (161 / 200 : ℝ)) ^ (10 / 9 : ℝ) =
      x ^ (181 / 1800 : ℝ) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_sub hx0]
    norm_num
  rw [hid] at hratio
  exact (Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num : (1 / 10 : ℝ) < 181 / 1800)).trans_le
    (hratio.trans hr0)

#print axioms caseOneSelectR
#print axioms goodProductPowerLower
end AmicableCases

