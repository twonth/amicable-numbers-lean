import SmallProductCount
import LogarithmicFactors

namespace AmicableStructure
open AmicableManuscript Filter
open scoped Topology

theorem smallProductSaving (c : ℝ) (hc : c < 1 / 2) : ∀ᶠ x : ℝ in atTop,
    ∀ (F : Finset ℕ) (m m' : ℕ → ℕ),
      (∀ n ∈ F, 0 < m n ∧ 0 < m' n) →
      (∀ n ∈ F, (m n : ℝ) * m' n ≤ x * Real.log x / L x ^ (1 / 2 : ℝ)) →
      (∀ n1 ∈ F, ∀ n2 ∈ F, m n1 = m n2 → m' n1 = m' n2 → n1 = n2) →
      (F.card : ℝ) ≤ x * L x ^ (-c) := by
  filter_upwards [AmicableScale.logarithmicFactorL (show 0 < 1 / 2 - c by linarith),
    AmicableScale.L_power_subpower (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2),
    AmicableScale.S_tendsto.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_gt_atTop (Real.exp 1)] with x hlog hL hS hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hx
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 < Real.log x := by
    have hh := Real.log_lt_log (Real.exp_pos 1) hx
    simpa using hh
  have hL0 : 0 < L x := Real.exp_pos _
  have hL1 : 1 ≤ L x := Real.one_le_exp_iff.mpr hS
  let T := x * Real.log x / L x ^ (1 / 2 : ℝ)
  have hT1 : 1 ≤ T := by
    have hpow : x ^ (1 / 2 : ℝ) ≤ x := by
      calc
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
        _ = _ := Real.rpow_one x
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL0 _)).mpr
    nlinarith
  have hTX : T ≤ x * Real.log x := by
    apply div_le_self (by positivity) (Real.one_le_rpow hL1 (by norm_num))
  have hfloorT : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT1)
  have hlogs : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log (⌊x * Real.log x⌋₊ : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊T⌋₊ by omega)) (Nat.cast_le.mpr (Nat.floor_mono hTX))
  have hK : ⌊Real.log ⌊T⌋₊ / Real.log 2⌋₊ + 1 ≤ ⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 :=
    Nat.add_le_add_right (Nat.floor_mono (div_le_div_of_nonneg_right hlogs (Real.log_pos (by norm_num)).le)) 1
  intro F m m' hpos hprod huniq
  have hh := smallProductCount F m m' (by linarith : 0 ≤ T) hpos hprod huniq
  calc
    (F.card : ℝ) ≤ 2 * T * (⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 : ℕ) :=
      hh.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hK) (by positivity))
    _ = x * (Real.log x * (2 * (⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 : ℕ))) / L x ^ (1 / 2 : ℝ) := by dsimp [T]; ring
    _ ≤ x * L x ^ (1 / 2 - c) / L x ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by rw [mul_div_assoc, ← Real.rpow_sub hL0]; congr 2; ring

#print axioms smallProductSaving
end AmicableStructure
