import PollackUniform

namespace AmicablePollack
open AmicableManuscript Filter
open scoped Topology

/-- Pollack's gcd estimate in the uniform form used in the manuscript. -/
theorem pollack {beta : ℝ} (hb : 0 < beta) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ X : ℝ in atTop, ∀ G : ℝ,
      Real.exp ((Real.log (Real.log X)) ^ beta) < G → ∀ F : Finset ℕ,
      (∀ n ∈ F, 0 < n ∧ (n : ℝ) ≤ X ∧ G < (Nat.gcd n (sigma n) : ℝ)) →
      (F.card : ℝ) ≤ X / G ^ rho := by
  classical
  obtain ⟨rho, hrho, hevent⟩ := gcdUniform (show 0 < beta / 2 by positivity)
  obtain ⟨G0, hG0⟩ := eventually_atTop.mp hevent
  refine ⟨rho, hrho, ?_⟩
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hpow := (tendsto_rpow_atTop hb).comp ht
  have hexp := Real.tendsto_exp_atTop.comp hpow
  have hhalf := (tendsto_rpow_atTop (show 0 < beta / 2 by positivity)).comp ht
  filter_upwards [hexp.eventually (eventually_ge_atTop G0),
    hhalf.eventually (eventually_ge_atTop (4 : ℝ)),
    ht.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (3 : ℝ)] with X hXG hXhalf hXt hX
  intro G hG F hF
  have hG0pos : 0 < G := (Real.exp_pos _).trans hG
  have hlogG : (Real.log (Real.log X)) ^ beta < Real.log G := by
    have hh := Real.log_lt_log (Real.exp_pos _) hG
    simpa only [Real.log_exp] using hh
  have hparam : Real.log (Real.log X) ≤ (Real.log G / 4) ^ (1 / (beta / 2)) := by
    let u := Real.log (Real.log X)
    have hu : 0 < u := hXt
    have hid : (u ^ (beta / 2)) ^ 2 = u ^ beta := by
      rw [← Real.rpow_mul_natCast hu.le]
      congr 1
      push_cast
      ring
    have hbase : u ^ (beta / 2) ≤ Real.log G / 4 := by
      have hprod := mul_le_mul_of_nonneg_right hXhalf (Real.rpow_nonneg hu.le (beta / 2))
      change 4 * u ^ (beta / 2) ≤ u ^ (beta / 2) * u ^ (beta / 2) at hprod
      nlinarith [hid]
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hu.le (beta / 2)) hbase
      (show 0 ≤ 1 / (beta / 2) by positivity)
    have hid2 : (u ^ (beta / 2)) ^ (1 / (beta / 2)) = u := by
      rw [← Real.rpow_mul hu.le]
      have he : beta / 2 * (1 / (beta / 2)) = 1 := by field_simp
      rw [he, Real.rpow_one]
    rw [hid2] at hh
    exact hh
  have hN : 3 ≤ ⌊X⌋₊ := Nat.le_floor hX
  have hlogN : Real.log (Real.log (⌊X⌋₊ : ℝ)) ≤ Real.log (Real.log X) := by
    apply Real.log_le_log
    · exact Real.log_pos (by exact_mod_cast (show 1 < ⌊X⌋₊ by omega))
    · exact Real.log_le_log (by exact_mod_cast (show 0 < ⌊X⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hh := hG0 G (hXG.trans hG.le) ⌊X⌋₊ F hN (hlogN.trans hparam) (by
    intro n hn
    exact ⟨(hF n hn).1, Nat.le_floor (hF n hn).2.1, (hF n hn).2.2⟩)
  calc
    (F.card : ℝ) ≤ (⌊X⌋₊ : ℝ) * G ^ (-rho) := hh
    _ ≤ X * G ^ (-rho) := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
    _ = X / G ^ rho := by rw [Real.rpow_neg hG0pos.le, div_eq_mul_inv]

#print axioms pollack
end AmicablePollack

