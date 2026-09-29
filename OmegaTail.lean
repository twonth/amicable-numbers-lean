import OmegaMoment
import RankinParameters

namespace AmicableOmega
open Filter
open scoped Topology BigOperators

noncomputable def tailRate (c C u : ℝ) : ℝ :=
    -c * (1 - 2 * Real.log (Real.log u) / Real.log u) +
      1 / Real.log u + C / (Real.log u) ^ 2

theorem tailRate_tendsto (c C : ℝ) : Tendsto (tailRate c C) atTop (𝓝 (-c)) := by
  have hinv : Tendsto (fun u : ℝ => (Real.log u)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hll : Tendsto (fun u : ℝ => Real.log (Real.log u) / Real.log u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hll.const_mul 2)).const_mul (-c)).add hinv
  have hh' := hh.add ((hinv.pow 2).const_mul C)
  change Tendsto (fun u => tailRate c C u) atTop (𝓝 (-c))
  simpa [tailRate, div_eq_mul_inv, inv_pow, mul_assoc] using hh'

theorem tailExponent (c C u : ℝ) (hu : 1 < u) :
    -(c * u / Real.log u) * Real.log (AmicableParameters.paramA u) +
      AmicableParameters.paramA u * (Real.log u + C) = tailRate c C u * u := by
  have hu0 : u ≠ 0 := by linarith
  have hl0 : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  unfold AmicableParameters.paramA tailRate
  rw [Real.log_div hu0 (pow_ne_zero _ hl0), Real.log_pow]
  push_cast
  field_simp
  ring

/-- A uniform form strong enough for Pollack's interval of divisors.
The cutoff for omega is set by A, while the counted integers may lie below any N<=A. -/
theorem omegaTailUniform {c : ℝ} (hc : 0 < c) :
    ∀ᶠ A : ℝ in atTop, ∀ (N : ℕ) (F : Finset ℕ), (N : ℝ) ≤ A →
      (∀ n ∈ F, 0 < n ∧ n ≤ N ∧ c * Real.log A / Real.log (Real.log A) ≤ (n.primeFactors.card : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) * A ^ (-c / 2) := by
  classical
  obtain ⟨C, hC⟩ := AmicableAnalytic.finiteMertens
  have hrate : ∀ᶠ u : ℝ in atTop, tailRate c C u ≤ -c / 2 := by
    filter_upwards [(tailRate_tendsto c C).eventually (gt_mem_nhds (by linarith : -c < -c / 2))]
      with u hu
    exact hu.le
  have hlogC : ∀ᶠ u : ℝ in atTop, 0 ≤ Real.log u + C := by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (-C))] with u hu
    linarith
  filter_upwards [Real.tendsto_log_atTop.eventually hrate,
    Real.tendsto_log_atTop.eventually hlogC,
    (AmicableParameters.paramA_tendsto.comp Real.tendsto_log_atTop).eventually_gt_atTop 1,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℝ)] with A hr hM hz hu hA
  intro N F hNA hF
  let P := Nat.primesBelow (N + 1)
  have hpP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hcover : ∀ n ∈ F, n.primeFactors ⊆ P := by
    intro n hn p hp
    apply Nat.mem_primesBelow.mpr
    exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (hF n hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans
      (hF n hn).2.1), Nat.prime_of_mem_primeFactors hp⟩
  have hprimeBound := hC A P hA (by
    intro p hp
    exact ⟨hpP p hp, (Nat.cast_le.mpr (Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hp).1)).trans hNA⟩)
  have hh := omegaTailFinite F P N (AmicableParameters.paramA (Real.log A))
    (c * Real.log A / Real.log (Real.log A)) (Real.log (Real.log A) + C) hz hF hpP hcover hprimeBound
  have hexp : (AmicableParameters.paramA (Real.log A) - 1) * (Real.log (Real.log A) + C) -
      (c * Real.log A / Real.log (Real.log A)) * Real.log (AmicableParameters.paramA (Real.log A)) ≤
      (-c / 2) * Real.log A := by
    have hid := tailExponent c C (Real.log A) hu
    have hmul := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ Real.log A)
    nlinarith
  refine hh.trans ?_
  rw [Real.rpow_def_of_pos (by linarith : 0 < A)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hexp])) (Nat.cast_nonneg N)

#print axioms tailRate_tendsto
#print axioms tailExponent
#print axioms omegaTailUniform
end AmicableOmega
