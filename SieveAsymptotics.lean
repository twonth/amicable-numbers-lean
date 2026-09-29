import ProgressionSieve
import ResidueCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace AmicableProgressions
open Filter
open scoped Topology

noncomputable def normalizedError (u : ℝ) : ℝ :=
  3 * u * (1 + u / 2) ^ 3 * Real.exp (-u / 2)

theorem normalizedError_tendsto : Tendsto normalizedError atTop (𝓝 0) := by
  have hk (k : ℕ) : Tendsto (fun u : ℝ => u ^ k * Real.exp (-u / 2)) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k (1 / 2) (by norm_num)
    simpa only [Real.rpow_natCast, neg_mul, one_div_mul_eq_div, neg_div] using hh
  have hh := (((hk 1).const_mul 3).add ((hk 2).const_mul (9 / 2))).add
    (((hk 3).const_mul (9 / 4)).add ((hk 4).const_mul (3 / 8)))
  convert hh using 1
  · ext u
    unfold normalizedError
    ring
  · norm_num

theorem sieveErrorEventually : ∀ᶠ u : ℝ in atTop,
    0 < u ∧ 3 * Real.exp (u / 2) * (1 + u / 2) ^ 3 ≤ Real.exp u / u := by
  filter_upwards [normalizedError_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with u hu hu0
  refine ⟨hu0, (le_div_iff₀ hu0).mpr ?_⟩
  have he : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = normalizedError u * Real.exp u := by unfold normalizedError; rw [mul_assoc _ _ (Real.exp u), he]; ring
    _ ≤ 1 * Real.exp u := mul_le_mul_of_nonneg_right hu.le (Real.exp_pos u).le
    _ = _ := one_mul _

theorem progressionTrivialBound (N q a : ℕ) (hq : 0 < q) :
    (primeCount N q a : ℝ) ≤ 1 + (N : ℝ) / q := by
  apply AmicableResidues.oneResidueRealBound _ hq (Nat.cast_nonneg N)
  intro n hn
  obtain ⟨hnA, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnN, hnmod⟩ := Finset.mem_filter.mp hnA
  exact ⟨Nat.cast_le.mpr (Finset.mem_range.mp hnN).le, hnmod⟩

theorem brunTitchmarshUniform : ∃ C : ℝ, 0 < C ∧
    ∀ N q a : ℕ, 0 < q → q < N → (primeCount N q a : ℝ) ≤
      C * N / ((q.totient : ℝ) * Real.log ((N : ℝ) / q)) := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp sieveErrorEventually
  let C : ℝ := max 5 (2 * max U 1)
  have hC5 : 5 ≤ C := le_max_left _ _
  have hCU : 2 * max U 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun N q a hq hqN => ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hq.trans hqN
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphiQ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  let t : ℝ := (N : ℝ) / q
  let u : ℝ := Real.log t
  let Z : ℝ := (N : ℝ) / ((q.totient : ℝ) * u)
  have ht1 : 1 < t := (one_lt_div hqR).mpr (by exact_mod_cast hqN)
  have hu : 0 < u := Real.log_pos ht1
  have ht : Real.exp u = t := Real.exp_log (by linarith)
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hratio : t / u ≤ Z := by
    have hh := div_le_div_of_nonneg_left hNR.le hphi hphiQ
    have hh' := div_le_div_of_nonneg_right hh hu.le
    simpa only [t, Z, div_div] using hh'
  change (primeCount N q a : ℝ) ≤ C * N / ((q.totient : ℝ) * u)
  suffices (primeCount N q a : ℝ) ≤ C * Z by simpa [Z, mul_div_assoc] using this
  by_cases hlarge : U ≤ u
  · have herr := (hU u hlarge).2
    have hz : 1 < Real.exp (u / 2) := Real.one_lt_exp_iff.mpr (by linarith)
    have hb := progressionPrimeBound N q a (Real.exp (u / 2)) hz hq
    rw [Real.log_exp] at hb
    have hmain : 2 * (N : ℝ) / ((q.totient : ℝ) * (u / 2)) = 4 * Z := by
      dsimp [Z]
      field_simp
      ring
    rw [hmain] at hb
    rw [ht] at herr
    have htotal : (primeCount N q a : ℝ) ≤ 5 * Z := by linarith [herr.trans hratio]
    exact htotal.trans (mul_le_mul_of_nonneg_right hC5 hZ0)
  · have hb := progressionTrivialBound N q a hq
    have huU : u ≤ max U 1 := (le_of_not_ge hlarge).trans (le_max_left _ _)
    have hCu : 2 * u ≤ C := by linarith
    calc
      (primeCount N q a : ℝ) ≤ 1 + t := hb
      _ ≤ 2 * t := by linarith
      _ = 2 * u * (t / u) := by field_simp
      _ ≤ C * (t / u) := mul_le_mul_of_nonneg_right hCu (by positivity)
      _ ≤ C * Z := mul_le_mul_of_nonneg_left hratio hC0.le

#print axioms brunTitchmarshUniform
#print axioms normalizedError_tendsto
#print axioms sieveErrorEventually
#print axioms progressionTrivialBound
end AmicableProgressions


