import ScaleBounds
import TechnicalExceptionalCount

namespace AmicableScale
open AmicableManuscript Filter
open scoped Topology

theorem constantLogPowerL (C k : ℝ) (hC : 0 ≤ C) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ k ≤ L x ^ a := by
  have htL : Tendsto L atTop atTop := Real.tendsto_exp_atTop.comp S_tendsto
  filter_upwards [log_power_L_subpower k (show 0 < a / 2 by positivity),
    ((tendsto_rpow_atTop (show 0 < a / 2 by positivity)).comp htL).eventually (eventually_ge_atTop C)]
      with x hx hCbound
  change C ≤ L x ^ (a / 2) at hCbound
  have hL0 : 0 < L x := Real.exp_pos (S x)
  calc
    C * (Real.log x) ^ k ≤ C * L x ^ (a / 2) := mul_le_mul_of_nonneg_left hx hC
    _ ≤ L x ^ (a / 2) * L x ^ (a / 2) := mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg hL0.le _)
    _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring

theorem dyadicLogBound {M : ℕ} {x : ℝ} (hM : 1 ≤ M) (hx : 1 ≤ Real.log x)
    (hMx : (M : ℝ) ≤ x ^ 2) (hx0 : 0 < x) :
    2 * (⌊Real.log M / Real.log 2⌋₊ + 1 : ℕ) ≤ (4 / Real.log 2 + 2) * (1 + Real.log x) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogM : Real.log (M : ℝ) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) hMx
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hf := Nat.floor_le (div_nonneg hlogM0 hlog2.le)
  have hh := div_le_div_of_nonneg_right hlogM hlog2.le
  have hi : 0 < 1 / Real.log 2 := one_div_pos.mpr hlog2
  push_cast
  simp only [div_eq_mul_inv, one_mul] at hf hh hi ⊢
  nlinarith

theorem logarithmicFactorL {a : ℝ} (ha : 0 < a) : ∀ᶠ x : ℝ in atTop,
    Real.log x * (2 * (⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 : ℕ)) ≤ L x ^ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ 2 * (4 / Real.log 2 + 2) := by positivity
  filter_upwards [constantLogPowerL (2 * (4 / Real.log 2 + 2)) 2 hC ha,
    eventually_gt_atTop (3 : ℝ)] with x hx hx3
  have hx0 : 0 < x := by linarith
  have hlog : 1 < Real.log x := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans hx3)
  have hX0 : 0 ≤ x * Real.log x := by positivity
  have hM : 1 ≤ ⌊x * Real.log x⌋₊ := Nat.le_floor (by norm_num; nlinarith)
  have hMx : (⌊x * Real.log x⌋₊ : ℝ) ≤ x ^ 2 := by
    have hh := Nat.floor_le hX0
    have hlogx := Real.log_le_sub_one_of_pos hx0
    nlinarith
  have hd := dyadicLogBound hM hlog.le hMx hx0
  have hh := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ Real.log x)
  have hcoef : 0 < 4 / Real.log 2 + 2 := by positivity
  have hmid : Real.log x * ((4 / Real.log 2 + 2) * (1 + Real.log x)) ≤
      2 * (4 / Real.log 2 + 2) * (Real.log x) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    have hprod := mul_nonneg hcoef.le (show 0 ≤ (Real.log x) ^ 2 - Real.log x by nlinarith)
    nlinarith
  exact hh.trans (hmid.trans hx)

#print axioms constantLogPowerL
#print axioms dyadicLogBound
#print axioms logarithmicFactorL
end AmicableScale

namespace AmicableTechnical
open AmicableManuscript AmicableWeight Filter
open scoped Topology

theorem exceptionalMultiplesSaving (k c : ℝ) (hc : c < k) : ∀ᶠ x : ℝ in atTop,
    ∀ F : Finset ℕ,
      (∀ n ∈ F, 0 < n ∧ (n : ℝ) ≤ x * Real.log x ∧ ∃ b : ℕ, b ∣ n ∧ Squarefree b ∧
        k * Real.log x < Real.log (smallPart (Real.log x) (sigma b)) +
          Real.log (Real.log x) * (roughOmega (Real.log x) (sigma b) : ℝ)) →
      (F.card : ℝ) ≤ x * L x ^ (-c) := by
  filter_upwards [exceptionalMultiples k,
    AmicableScale.logarithmicFactorL (show 0 < (k - c) / 2 by linarith),
    (errorX_tendsto k).eventually (gt_mem_nhds (show 0 < (k - c) / 2 by linarith)),
    AmicableScale.S_tendsto.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hx hlog herr hS hx1
  intro F hF
  have hL : 1 ≤ L x := Real.one_le_exp_iff.mpr hS
  have hL0 : 0 < L x := Real.exp_pos _
  have hp := Real.rpow_le_rpow_of_exponent_le hL (show -k + errorX k x + (k - c) / 2 ≤ -c by linarith)
  have hh := hx F hF
  calc
    (F.card : ℝ) ≤ x * (Real.log x * (2 * (⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 : ℕ))) *
        L x ^ (-k + errorX k x) := by convert hh using 1 <;> ring
    _ ≤ x * L x ^ ((k - c) / 2) * L x ^ (-k + errorX k x) := by gcongr
    _ = x * L x ^ (-k + errorX k x + (k - c) / 2) := by
      rw [mul_assoc, ← Real.rpow_add hL0]; congr 2; ring
    _ ≤ x * L x ^ (-c) := mul_le_mul_of_nonneg_left hp (by linarith)

#print axioms exceptionalMultiplesSaving
end AmicableTechnical

