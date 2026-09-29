import RankinParameters
import ManuscriptArithmetic

namespace AmicableScale
open AmicableManuscript AmicableParameters Filter
open scoped Topology

theorem scale_tendsto : Tendsto scale atTop atTop := by
  have hh := (tendsto_exp_div_rpow_atTop (1 : ℝ)).atTop_mul_atTop₀ Real.tendsto_log_atTop
  change Tendsto (fun t : ℝ => Real.exp t * Real.log t / t) atTop atTop
  simpa only [Real.rpow_one, div_mul_eq_mul_div] using hh

theorem S_tendsto : Tendsto S atTop atTop := by
  have hh := scale_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply, scale, S, Real.exp_log (Real.log_pos hx)]

theorem S_div_log_tendsto : Tendsto (fun x => S x / Real.log x) atTop (𝓝 0) := by
  have hh := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp [S]
  field_simp [(Real.log_pos hx).ne']

theorem loglog_div_S_tendsto :
    Tendsto (fun x => Real.log (Real.log x) / S x) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 1 (by norm_num)
  have hi := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hh : Tendsto (fun t : ℝ => t / scale t) atTop (𝓝 0) := by
    have hp := he.mul hi
    apply (show Tendsto (fun t : ℝ => (t ^ 2 * Real.exp (-t)) * (Real.log t)⁻¹)
      atTop (𝓝 0) by simpa using hp).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    dsimp [scale]
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos t).ne', (Real.log_pos ht).ne', (by linarith : t ≠ 0)]
  have hout := hh.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply hout.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply, scale, S, Real.exp_log (Real.log_pos hx)]

theorem L_power_subpower (C : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, L x ^ C ≤ x ^ e := by
  have hh := S_div_log_tendsto.const_mul C
  filter_upwards [hh.eventually (gt_mem_nhds (by simpa using he)), eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hxlog := Real.log_pos hx1
  have hprod : C * S x ≤ e * Real.log x := by
    have h := (div_lt_iff₀ hxlog).mp (show C * S x / Real.log x < e by simpa [mul_div_assoc] using hx)
    exact h.le
  unfold L
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem log_power_L_subpower (k : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ k ≤ L x ^ e := by
  have hh := loglog_div_S_tendsto.const_mul k
  filter_upwards [hh.eventually (gt_mem_nhds (by simpa using he)), S_tendsto.eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (1 : ℝ)] with x hx hS hx1
  have hprod : k * Real.log (Real.log x) ≤ e * S x := by
    have h := (div_lt_iff₀ hS).mp
      (show k * Real.log (Real.log x) / S x < e by simpa [mul_div_assoc] using hx)
    exact h.le
  unfold L
  rw [Real.rpow_def_of_pos (Real.log_pos hx1),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  exact Real.exp_le_exp.mpr (by nlinarith)

#print axioms scale_tendsto
#print axioms S_tendsto
#print axioms S_div_log_tendsto
#print axioms loglog_div_S_tendsto
#print axioms L_power_subpower
#print axioms log_power_L_subpower
end AmicableScale

