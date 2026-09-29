import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace AmicableParameters
open Filter
open scoped Topology

/-! The variable t is log_2 x. Keeping it separate makes the exact error terms
visible; no unspecified o(1) is introduced as an assumption. -/
noncomputable def paramA (t : ℝ) : ℝ := t / (Real.log t) ^ 2
noncomputable def eta (t : ℝ) : ℝ := Real.log (paramA t) / t
noncomputable def delta (t : ℝ) : ℝ := 1 / t

theorem paramA_pos {t : ℝ} (ht : 1 < t) : 0 < paramA t := by
  exact div_pos (by linarith) (sq_pos_of_pos (Real.log_pos ht))

theorem paramA_tendsto : Tendsto paramA atTop atTop := by
  have hz : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).tendsto_div_nhds_zero
  have hz' : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact div_pos (sq_pos_of_pos (Real.log_pos ht)) (by linarith)
  change Tendsto (fun t : ℝ => t / (Real.log t) ^ 2) atTop atTop
  apply hz'.inv_tendsto_nhdsGT_zero.congr
  intro t
  change ((Real.log t) ^ 2 / t)⁻¹ = t / (Real.log t) ^ 2
  rw [inv_div]

theorem delta_tendsto : Tendsto delta atTop (𝓝[>] 0) := by
  change Tendsto (fun t : ℝ => 1 / t) atTop (𝓝[>] 0)
  simpa only [one_div] using (tendsto_inv_atTop_nhdsGT_zero :
    Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝[>] 0))

theorem eta_identity {t : ℝ} (ht : 1 < t) :
    eta t = (Real.log t - 2 * Real.log (Real.log t)) / t := by
  unfold eta paramA
  rw [Real.log_div (by linarith) (pow_ne_zero _ (Real.log_pos ht).ne'), Real.log_pow]
  norm_num

theorem eta_tendsto : Tendsto eta atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) :=
    hl.comp Real.tendsto_log_atTop
  have hprod := hll.mul hl
  have hprod0 : Tendsto (fun t : ℝ => (Real.log (Real.log t) / Real.log t) *
      (Real.log t / t)) atTop (𝓝 0) := by simpa using hprod
  have hll' : Tendsto (fun t : ℝ => Real.log (Real.log t) / t) atTop (𝓝 0) := by
    apply hprod0.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    field_simp
  have hout := hl.sub (hll'.const_mul 2)
  have hout0 : Tendsto (fun t : ℝ => Real.log t / t - 2 * (Real.log (Real.log t) / t))
      atTop (𝓝 0) := by simpa using hout
  apply hout0.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [eta_identity ht]
  ring

theorem eta_eventually_admissible : ∀ᶠ t : ℝ in atTop, 0 < eta t ∧ eta t ≤ 1 / 4 := by
  filter_upwards [paramA_tendsto.eventually_gt_atTop 1,
    eta_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_gt_atTop (1 : ℝ)] with t hA he ht
  exact ⟨div_pos (Real.log_pos hA) (by linarith), he.le⟩

theorem exp_rpow_eta {t : ℝ} (ht : 1 < t) :
    (Real.exp t) ^ eta t = paramA t := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  unfold eta
  rw [mul_div_cancel₀ _ (by linarith : t ≠ 0)]
  exact Real.exp_log (paramA_pos ht)

theorem momentExponentRatio (C K : ℝ) :
    Tendsto (fun t : ℝ => (paramA t * (2 * Real.log t + C) + K) / t)
      atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have ht : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun t : ℝ => 2 * (Real.log t)⁻¹ +
      C * ((Real.log t)⁻¹) ^ 2 + K * t⁻¹) atTop (𝓝 0) := by
    simpa using ((hl.const_mul 2).add ((hl.pow 2).const_mul C)).add (ht.const_mul K)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  unfold paramA
  field_simp

theorem momentExponent_eventually (C K : ℝ) :
    ∀ᶠ t : ℝ in atTop, paramA t * (2 * Real.log t + C) + K ≤ t / 2 := by
  filter_upwards [(momentExponentRatio C K).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_gt_atTop (0 : ℝ)]
    with t h ht
  have hh := (div_lt_iff₀ ht).mp h
  linarith

noncomputable def scale (t : ℝ) : ℝ := Real.exp t * Real.log t / t

noncomputable def error (k t : ℝ) : ℝ :=
  2 * k * (Real.log (Real.log t) / Real.log t) +
    (1 + t * Real.exp (-t)) / Real.log t +
    3 * (t * Real.exp (-(1 / 2 : ℝ) * t)) / Real.log t

theorem error_tendsto (k : ℝ) : Tendsto (error k) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hexp1 : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)
  have hexp2 : Tendsto (fun t : ℝ => t * Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
  have hlim := ((hll.const_mul (2 * k)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).add hexp1).mul hl)).add ((hexp2.const_mul 3).mul hl)
  change Tendsto (fun t : ℝ => error k t) atTop (𝓝 0)
  simpa [error, div_eq_mul_inv] using hlim

theorem exponentIdentity {t : ℝ} (ht : 1 < t) (k : ℝ) :
    (Real.exp t + t) / t - k * Real.exp t * eta t + 3 * Real.exp (t / 2) =
      (-k + error k t) * scale t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have he1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  have he2 : Real.exp (-(1 / 2 : ℝ) * t) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [eta_identity ht]
  unfold error scale
  field_simp
  have he2' : Real.exp (-(t / 2)) * Real.exp t = Real.exp (t / 2) := by
    convert he2 using 1 <;> congr 2 <;> ring
  linear_combination -t * he1 - 3 * t * he2'

#print axioms exponentIdentity
#print axioms momentExponentRatio
#print axioms momentExponent_eventually
#print axioms error_tendsto

#print axioms paramA_pos
#print axioms paramA_tendsto
#print axioms delta_tendsto
#print axioms eta_identity
#print axioms eta_tendsto
#print axioms eta_eventually_admissible
#print axioms exp_rpow_eta
end AmicableParameters

