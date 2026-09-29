import StructuralFactorization
import UnitaryFactors
import ScaleBounds
import SigmaUniform

namespace AmicableStructure
open AmicableManuscript Filter
open scoped Topology

/-- The uniform quantitative content of Proposition 3, for one chosen ordering. -/
structure RegularPair (x C : ℝ) (n n' : ℕ) : Prop where
  pair : Amicable n n'
  bound : (n : ℝ) ≤ x * Real.log x
  bound' : (n' : ℝ) ≤ x * Real.log x
  factors : ∃ a a' B B' : ℕ,
    n = B * a ∧ n' = B' * a' ∧ Squarefree a ∧ Squarefree a' ∧
    B.Coprime a ∧ B'.Coprime a' ∧ a.Coprime n' ∧ a'.Coprime n ∧
    x / L x ^ C ≤ (a : ℝ) ∧ x / L x ^ C ≤ (a' : ℝ) ∧
    (B : ℝ) ≤ L x ^ C ∧ (B' : ℝ) ≤ L x ^ C ∧
    a'.maxPrimeFac < a.maxPrimeFac ∧ (a.maxPrimeFac : ℝ) ≤ x ^ (4 / 5 : ℝ)

theorem regularSizeBounds (C : ℝ) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ a B : ℕ,
      x / L x ^ C ≤ (a : ℝ) → (a : ℝ) ≤ x * Real.log x →
      (B : ℝ) ≤ L x ^ C → 0 < B →
      1 < a ∧ (1 - eta) * Real.log x ≤ Real.log (a : ℝ) ∧
      Real.log (a : ℝ) ≤ (1 + eta) * Real.log x ∧
      Real.log (sigma B : ℝ) ≤ eta * Real.log x := by
  filter_upwards [AmicableScale.L_power_subpower C (show 0 < eta / 2 by positivity),
    AmicableSigmaBounds.sigmaUniformRatio (show 0 < eta / 2 by positivity),
    AmicableAbsorption.constantLogAbsorb 1 heta,
    eventually_gt_atTop (Real.exp 1)] with x hL hsigma hlog hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hx
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 < Real.log x := by
    have hh := Real.log_lt_log (Real.exp_pos 1) hx
    simpa using hh
  have hlog0 : 0 < Real.log x := by linarith
  have hL0 : 0 < L x ^ C := Real.rpow_pos_of_pos (Real.exp_pos _) _
  intro a B halower haupper hB hBpos
  have halo : x ^ (1 - eta / 2) ≤ (a : ℝ) := by
    calc
      _ = x / x ^ (eta / 2) := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ x / L x ^ C := div_le_div_of_nonneg_left hx0.le hL0 hL
      _ ≤ _ := halower
  have haone : 1 < a := by
    have hh := Real.one_lt_rpow hx1 (show 0 < 1 - eta / 2 by linarith)
    exact_mod_cast hh.trans_le halo
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hBpow : (B : ℝ) ≤ x ^ (eta / 2) := hB.trans hL
  have hBX : (B : ℝ) ≤ x * Real.log x := by
    have hp : x ^ (eta / 2) ≤ x := by
      calc
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = x := Real.rpow_one x
    nlinarith
  refine ⟨haone, ?_, ?_, ?_⟩
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) halo
    rw [Real.log_rpow hx0] at hh
    nlinarith
  · have hh : (a : ℝ) ≤ x ^ (1 + eta) := by
      calc
        _ ≤ x * Real.log x := haupper
        _ ≤ x * x ^ eta := by gcongr; linarith
        _ = x ^ (1 + eta) := by rw [Real.rpow_add hx0, Real.rpow_one]
    have hhl := Real.log_le_log hapos hh
    simpa only [Real.log_rpow hx0] using hhl
  · have hh : (sigma B : ℝ) ≤ x ^ eta := by
      calc
        _ ≤ (B : ℝ) * x ^ (eta / 2) := hsigma _ hBX
        _ ≤ x ^ (eta / 2) * x ^ (eta / 2) := by gcongr
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    have hspos : (0 : ℝ) < sigma B := by
      exact_mod_cast (show 0 < sigma B by rw [sigma_eq_s_add_self]; omega)
    simpa only [Real.log_rpow hx0] using Real.log_le_log hspos hh

#print axioms regularSizeBounds
end AmicableStructure
