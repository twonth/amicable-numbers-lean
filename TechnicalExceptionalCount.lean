import TechnicalLemma
import ManyPrimeDivisors

namespace AmicableTechnical
open AmicableManuscript AmicableWeight Filter
open scoped Topology BigOperators

theorem exceptionalMultiples (k : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ F : Finset ℕ,
      (∀ n ∈ F, 0 < n ∧ (n : ℝ) ≤ x * Real.log x ∧ ∃ b : ℕ, b ∣ n ∧ Squarefree b ∧
        k * Real.log x < Real.log (smallPart (Real.log x) (sigma b)) +
          Real.log (Real.log x) * (roughOmega (Real.log x) (sigma b) : ℝ)) →
      (F.card : ℝ) ≤ (x * Real.log x) *
        (2 * L x ^ (-k + errorX k x) * (⌊Real.log ⌊x * Real.log x⌋₊ / Real.log 2⌋₊ + 1 : ℕ)) := by
  classical
  filter_upwards [technicalLemma k, eventually_gt_atTop (3 : ℝ)] with x hx hx3
  intro F hF
  let X := x * Real.log x
  let N := ⌊X⌋₊
  let D := exceptionalSet k x X
  let E := L x ^ (-k + errorX k x)
  have hX : 1 ≤ X := by
    have hlog : 1 < Real.log x := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans hx3)
    dsimp [X]; nlinarith
  have hE : 0 ≤ E := Real.rpow_nonneg (Real.exp_pos _).le _
  have hD : ∀ b ∈ D, 0 < b ∧ b ≤ N := by
    intro b hb
    obtain ⟨hbN, hbsf, _⟩ := Finset.mem_filter.mp hb
    exact ⟨Nat.pos_of_ne_zero hbsf.ne_zero, Nat.le_of_lt_succ (Finset.mem_range.mp hbN)⟩
  have hrec := AmicablePartialSummation.reciprocalFromCount D N E hE hD (by
    intro T hT
    by_cases hTN : T ≤ N
    · have hTX : (T : ℝ) ≤ X := (by exact_mod_cast hTN : (T : ℝ) ≤ N).trans (Nat.floor_le (by linarith))
      have hsub : D.filter (· ≤ T) ⊆ exceptionalSet k x T := by
        intro b hb
        obtain ⟨hbD, hbT⟩ := Finset.mem_filter.mp hb
        obtain ⟨_, hbad⟩ := Finset.mem_filter.mp hbD
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simpa using Nat.lt_succ_of_le hbT), hbad⟩
      have hc : ((D.filter (· ≤ T)).card : ℝ) ≤ (exceptionalSet k x T).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
      exact hc.trans (by simpa [E, mul_comm] using hx T (by exact_mod_cast hT) hTX)
    · have hsub : D.filter (· ≤ T) ⊆ D := Finset.filter_subset _ _
      have hN1 : 1 ≤ N := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ X by simpa using hX)
      have hDN : D = exceptionalSet k x N := by
        ext b
        simp only [D, exceptionalSet, Nat.floor_natCast, N]
      have hc := hx N (by exact_mod_cast hN1) (Nat.floor_le (by linarith : 0 ≤ X))
      rw [← hDN] at hc
      have hh : (N : ℝ) ≤ T := by exact_mod_cast (le_of_not_ge hTN)
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hc.trans (by simpa [E, mul_comm] using mul_le_mul_of_nonneg_right hh hE)))
  have hmult := AmicableGcdCounting.divisorMultipleFamilyCount F D N (fun b hb => (hD b hb).1) (by
    intro n hn
    obtain ⟨hn0, hnX, b, hbn, hbsf, hbad⟩ := hF n hn
    refine ⟨hn0, Nat.le_floor hnX, b, ?_, hbn⟩
    have hbX : (b : ℝ) ≤ X := (by exact_mod_cast Nat.le_of_dvd hn0 hbn : (b : ℝ) ≤ n).trans hnX
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hbX)), hbsf, hbad⟩)
  exact hmult.trans (mul_le_mul (Nat.floor_le (by linarith : 0 ≤ X)) hrec
    (Finset.sum_nonneg (fun _ _ => by positivity)) (by linarith))

#print axioms exceptionalMultiples
end AmicableTechnical

