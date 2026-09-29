import ScaleBounds

namespace AmicableScale
open AmicableManuscript Filter
open scoped Topology

theorem powerSavingL (c : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 - eta) ≤ x * L x ^ (-c) := by
  filter_upwards [L_power_subpower c heta, eventually_gt_atTop (0 : ℝ)] with x hL hx
  have hL0 : 0 < L x := Real.exp_pos _
  calc
    x ^ (1 - eta) = x / x ^ eta := by rw [Real.rpow_sub hx, Real.rpow_one]
    _ ≤ x / L x ^ c := div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos (Real.exp_pos _) _) hL
    _ = x * L x ^ (-c) := by rw [Real.rpow_neg hL0.le, div_eq_mul_inv]

theorem constantLAbsorb (C : ℝ) (hC : 0 < C) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, C ≤ L x ^ eta := by
  filter_upwards [S_tendsto.eventually (eventually_ge_atTop (Real.log C / eta))] with x hx
  have hh : Real.log C ≤ S x * eta := (div_le_iff₀ heta).mp hx
  have he := Real.exp_le_exp.mpr hh
  simpa only [Real.exp_log hC, L, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] using he

theorem combineSavings {c c' : ℝ} (hc : c < c') (K : ℝ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, K * (x * L x ^ (-c')) ≤ x * L x ^ (-c) := by
  filter_upwards [constantLAbsorb K hK (show 0 < c' - c by linarith),
    eventually_gt_atTop (0 : ℝ)] with x hKx hx
  have hL0 : 0 < L x := Real.exp_pos _
  calc
    _ ≤ L x ^ (c' - c) * (x * L x ^ (-c')) := mul_le_mul_of_nonneg_right hKx (by positivity)
    _ = x * L x ^ (-c) := by
      rw [mul_left_comm, ← mul_assoc, mul_assoc x, ← Real.rpow_add hL0]
      congr 2
      ring

#print axioms powerSavingL
#print axioms constantLAbsorb
#print axioms combineSavings
end AmicableScale
