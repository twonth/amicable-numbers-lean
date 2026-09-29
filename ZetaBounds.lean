import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Tactic

namespace AmicableZeta
open ArithmeticFunction
open Filter
open scoped Topology


theorem logSummand_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ vonMangoldt n / ((n : ℝ) ^ s * Real.log n) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  exact div_nonneg vonMangoldt_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.log_nonneg hn1))

theorem logSummand_le (s : ℝ) (n : ℕ) :
    vonMangoldt n / ((n : ℝ) ^ s * Real.log n) ≤ 1 / (n : ℝ) ^ s := by
  by_cases hn0 : n = 0
  · simp [hn0]; positivity
  by_cases hn1 : n = 1
  · simp [hn1]
  have hn : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnp : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 0 < Real.log n := Real.log_pos hn
  rw [div_le_div_iff₀ (mul_pos hnp hlog) hnp]
  nlinarith [mul_le_mul_of_nonneg_right (vonMangoldt_le_log (n := n)) hnp.le]

theorem logSummand_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt n / ((n : ℝ) ^ s * Real.log n)) :=
  Summable.of_nonneg_of_le (logSummand_nonneg s) (logSummand_le s)
    (Real.summable_one_div_nat_rpow.mpr hs)

theorem primeSum_le_log_zeta {s : ℝ} (hs : 1 < s) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, 1 / (p : ℝ) ^ s ≤ Real.log (riemannZeta (s : ℂ)).re := by
  rw [log_riemannZeta_eq hs]
  have heq : ∑ p ∈ P, 1 / (p : ℝ) ^ s =
      ∑ p ∈ P, vonMangoldt p / ((p : ℝ) ^ s * Real.log p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (hP p hp)]
    have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast (hP p hp).one_lt)).ne'
    field_simp
  rw [heq]
  exact (logSummand_summable hs).sum_le_tsum P (fun n _ => logSummand_nonneg s n)

theorem realZeta_eq {s : ℝ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  have hcomplex : riemannZeta (s : ℂ) =
      ((∑' n : ℕ, 1 / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs), Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hcomplex]
  simp

/-- The standard estimate log zeta(1+delta) <= log(1/delta)+O(1),
with the O(1) replaced by the explicit constant log 2 sufficiently near zero. -/
theorem log_zeta_near_one :
    ∀ᶠ delta : ℝ in 𝓝[>] 0,
      Real.log (riemannZeta ((1 + delta : ℝ) : ℂ)).re ≤
        Real.log (1 / delta) + Real.log 2 := by
  have hshift : Tendsto (fun delta : ℝ => 1 + delta) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun delta : ℝ => (1 : ℝ) + delta) := by fun_prop
      have ht0 : Tendsto (fun delta : ℝ => (1 : ℝ) + delta) (𝓝 0) (𝓝 1) := by
        convert hc.continuousAt.tendsto (x := 0) using 1 <;> norm_num
      exact ht0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with delta hd
      simpa using hd
  have ht := tendsto_sub_mul_tsum_nat_rpow.comp hshift
  have hb : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      delta * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + delta)) < 2 := by
    simpa using ht.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hb, self_mem_nhdsWithin] with delta hbd hd
  have hdpos : 0 < delta := hd
  have hs : 1 < 1 + delta := by linarith
  rw [realZeta_eq hs]
  have hzpos : 0 < ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + delta) := by
    rw [← realZeta_eq hs]
    exact riemannZeta_re_pos_of_one_lt hs
  have hzle : (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + delta)) ≤ 2 / delta := by
    apply (le_div_iff₀ hdpos).mpr
    nlinarith
  calc
    _ ≤ Real.log (2 / delta) := Real.log_le_log hzpos hzle
    _ = Real.log (1 / delta) + Real.log 2 := by
      rw [Real.log_div (by norm_num) hdpos.ne', Real.log_div (by norm_num) hdpos.ne']
      simp
      ring

#print axioms logSummand_nonneg
#print axioms logSummand_le
#print axioms logSummand_summable
#print axioms primeSum_le_log_zeta
#print axioms realZeta_eq
#print axioms log_zeta_near_one
end AmicableZeta
