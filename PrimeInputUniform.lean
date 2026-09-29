import SigmaReciprocals
import AsymptoticAbsorption

namespace AmicableSigmaCounting
open Filter
open scoped Topology BigOperators

theorem primeInputUniform : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    1 ≤ Real.log (Real.log x) ∧ ∀ M : ℕ, 3 ≤ M → (M : ℝ) ≤ x * Real.log x →
    ∀ d : ℕ, 0 < d →
      ∑ p ∈ (Finset.range (M + 1)).filter (fun p => p.Prime ∧ d ∣ p + 1), (1 : ℝ) / p ≤
        (C * Real.log (Real.log x)) / d.totient := by
  obtain ⟨C, hC, hc⟩ := primeReciprocalInput
  refine ⟨3 * C, by linarith, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ)), eventually_gt_atTop (1 : ℝ)] with x ht hx
  change 1 ≤ Real.log (Real.log x) at ht
  refine ⟨ht, ?_⟩
  intro M hM hMX d hd
  have hx0 : 0 < x := by linarith
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hMxx : (M : ℝ) ≤ x ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos hx0
    nlinarith
  have hlog : Real.log (M : ℝ) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log hm0 hMxx
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hll : Real.log (Real.log (M : ℝ)) ≤ 2 * Real.log (Real.log x) := by
    have hh := Real.log_le_log hlogM hlog
    rw [Real.log_mul (by norm_num) (Real.log_pos hx).ne'] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  apply (hc M hM d hd).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith

theorem partitionErrorAbsorb (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (Real.log (2 * C) * Real.log x / Real.log (Real.log x)) ≤ x ^ a := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hz : Tendsto (fun x : ℝ => Real.log (2 * C) / Real.log (Real.log x)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul (Real.log (2 * C))
  filter_upwards [hz.eventually (gt_mem_nhds ha), eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hx.le (Real.log_pos hx1).le
  convert hh using 1 <;> ring

#print axioms primeInputUniform
#print axioms partitionErrorAbsorb
end AmicableSigmaCounting

