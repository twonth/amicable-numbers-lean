import SieveAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

namespace AmicablePrimeReciprocals
open AmicableProgressions
open scoped BigOperators

theorem shellReciprocalBound {C : ℝ} (hC : 0 < C)
    (hBT : ∀ N q a : ℕ, 0 < q → q < N → (primeCount N q a : ℝ) ≤
      C * N / ((q.totient : ℝ) * Real.log ((N : ℝ) / q)))
    (P : Finset ℕ) (d a k : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.ModEq d p a ∧ d * 2 ^ k ≤ p ∧ p < d * 2 ^ (k + 1)) :
    ∑ p ∈ P, (1 : ℝ) / p ≤ (2 * C / ((d.totient : ℝ) * Real.log 2)) * (1 / ((k : ℝ) + 1)) := by
  classical
  let N := d * 2 ^ (k + 1)
  have hsub : P ⊆ (((Finset.range N).filter (fun n => Nat.ModEq d n a)).filter Nat.Prime) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hP p hp).2.2.2, (hP p hp).2.1⟩, (hP p hp).1⟩
  have hdN : d < N := by
    have hh : 1 < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
    dsimp [N]
    nlinarith
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hBT N d a hd hdN)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log ((N : ℝ) / d) = (k + 1 : ℕ) * Real.log 2 := by
    dsimp [N]
    push_cast
    rw [mul_div_cancel_left₀ _ hdR.ne', Real.log_pow]
    push_cast
    rfl
  have hsum : ∑ p ∈ P, (1 : ℝ) / p ≤ (P.card : ℝ) / ((d : ℝ) * 2 ^ k) := by
    calc
      _ ≤ ∑ p ∈ P, (1 : ℝ) / ((d : ℝ) * 2 ^ k) := Finset.sum_le_sum (by
        intro p hp
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (hP p hp).2.2.1))
      _ = _ := by simp [div_eq_mul_inv]
  refine hsum.trans ((div_le_div_of_nonneg_right hcard (by positivity)).trans_eq ?_)
  rw [hlogN]
  dsimp [N]
  push_cast
  rw [pow_succ]
  field_simp

theorem reciprocalAboveModulus {C : ℝ} (hC : 0 < C)
    (hBT : ∀ N q a : ℕ, 0 < q → q < N → (primeCount N q a : ℝ) ≤
      C * N / ((q.totient : ℝ) * Real.log ((N : ℝ) / q)))
    (P : Finset ℕ) (d a N : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.ModEq d p a ∧ d ≤ p ∧ p ≤ N) :
    ∑ p ∈ P, (1 : ℝ) / p ≤ (2 * C / ((d.totient : ℝ) * Real.log 2)) *
      ∑ k ∈ Finset.range (⌊Real.log N / Real.log 2⌋₊ + 1), (1 : ℝ) / (k + 1) := by
  classical
  let K := ⌊Real.log N / Real.log 2⌋₊
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcover : ∀ p ∈ P, ∃ k : ℕ, k ≤ K ∧ d * 2 ^ k ≤ p ∧ p < d * 2 ^ (k + 1) := by
    intro p hp
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := (p : ℝ) / d)
      ((one_le_div hdR).mpr (by exact_mod_cast (hP p hp).2.2.1))
      (by norm_num : (1 : ℝ) < 2)
    have hklo : (d : ℝ) * 2 ^ k ≤ p := by
      have hh := (le_div_iff₀ hdR).mp hk1
      linarith
    have hkhi : (p : ℝ) < (d : ℝ) * 2 ^ (k + 1) := by
      have hh := (div_lt_iff₀ hdR).mp hk2
      linarith
    refine ⟨k, ?_, by exact_mod_cast hklo, by exact_mod_cast hkhi⟩
    have hpowN : (2 : ℝ) ^ k ≤ N := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hpN : (p : ℝ) ≤ N := by exact_mod_cast (hP p hp).2.2.2
      have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
      nlinarith
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ k) hpowN
    rw [Real.log_pow] at hh
    apply Nat.le_floor
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hh
  choose! idx hidx using hcover
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (hidx p hp).1))
    (fun p : ℕ => (1 : ℝ) / p)
  rw [← hsplit]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply shellReciprocalBound hC hBT _ d a k hd
  intro p hp
  obtain ⟨hpP, hpk⟩ := Finset.mem_filter.mp hp
  exact ⟨(hP p hpP).1, (hP p hpP).2.1, hpk ▸ (hidx p hpP).2⟩

theorem shiftedHarmonicBound (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (1 : ℝ) / (k + 1) ≤ 1 + Real.log (K + 1 : ℕ) := by
  have heq : ∑ k ∈ Finset.range (K + 1), (1 : ℝ) / (k + 1) =
      ∑ j ∈ Finset.Icc 1 (K + 1), (1 : ℝ) / j := by
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      simp only [Finset.mem_range] at hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k hk l hl h
      omega
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      push_cast
      rfl
  rw [heq]
  simpa only [one_div] using Aux.sum_inv_le_log (K + 1) (by omega)

noncomputable def harmonicConstant : ℝ := 1 + Real.log (1 + 1 / Real.log 2)

theorem harmonicConstant_pos : 0 < harmonicConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 1 < 1 + 1 / Real.log 2 := by linarith [one_div_pos.mpr hlog]
  unfold harmonicConstant
  linarith [Real.log_pos harg]

theorem dyadicHarmonicBound (N : ℕ) (hN : 3 ≤ N) :
    ∑ k ∈ Finset.range (⌊Real.log N / Real.log 2⌋₊ + 1), (1 : ℝ) / (k + 1) ≤
      harmonicConstant * (1 + Real.log (Real.log N)) := by
  let K := ⌊Real.log N / Real.log 2⌋₊
  let D : ℝ := 1 + 1 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 1 < Real.log (N : ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans_le (show (3 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN))
    simpa only [Real.log_exp] using hh
  have hD : 1 < D := by dsimp [D]; linarith [one_div_pos.mpr hlog2]
  have hupper : (K + 1 : ℕ) ≤ D * Real.log N := by
    have hh := Nat.floor_le (div_nonneg (by linarith : 0 ≤ Real.log (N : ℝ)) hlog2.le)
    change (K : ℝ) ≤ _ at hh
    push_cast
    calc
      (K : ℝ) + 1 ≤ Real.log N / Real.log 2 + 1 := by linarith
      _ ≤ Real.log N / Real.log 2 + Real.log N := by linarith
      _ = _ := by dsimp [D]; ring
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) < (K + 1 : ℕ)) hupper
  rw [Real.log_mul (by linarith : D ≠ 0) (by linarith : Real.log (N : ℝ) ≠ 0)] at hlogs
  have hlogD : 0 ≤ Real.log D := (Real.log_pos hD).le
  have hloglog : 0 ≤ Real.log (Real.log (N : ℝ)) := (Real.log_pos hlogN).le
  have hh := shiftedHarmonicBound K
  change _ ≤ (1 + Real.log D) * (1 + Real.log (Real.log N))
  nlinarith [mul_nonneg hlogD hloglog]

#print axioms shiftedHarmonicBound
#print axioms harmonicConstant_pos
#print axioms dyadicHarmonicBound
#print axioms shellReciprocalBound
#print axioms reciprocalAboveModulus
end AmicablePrimeReciprocals



namespace AmicablePrimeReciprocals

theorem belowModulus (P : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, p.Prime ∧ d ∣ p + 1 ∧ p < d) :
    ∑ p ∈ P, (1 : ℝ) / p ≤ 2 / (d.totient : ℝ) := by
  classical
  have hsub : P ⊆ {d - 1} := by
    intro p hp
    have hpd := (hP p hp).2.2
    have heq : p + 1 = d := Nat.le_antisymm (by omega) (Nat.le_of_dvd (by omega) (hP p hp).2.1)
    simpa only [Finset.mem_singleton] using (show p = d - 1 by omega)
  by_cases he : P = ∅
  · simp only [he, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hp2 := (hP p hp).1.two_le
  have hpd : p = d - 1 := by simpa only [Finset.mem_singleton] using hsub hp
  have hd2 : 2 ≤ d := by have := (hP p hp).2.2; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hdm : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (show 0 < d - 1 by omega)
  calc
    _ ≤ ∑ p ∈ ({d - 1} : Finset ℕ), (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 / (d - 1 : ℕ) := by simp
    _ ≤ 2 / (d : ℝ) := by
      apply (div_le_div_iff₀ hdm hdR).mpr
      have hh : d ≤ 2 * (d - 1) := by omega
      simpa only [one_mul] using (show (d : ℝ) ≤ 2 * (d - 1 : ℕ) by exact_mod_cast hh)
    _ ≤ 2 / (d.totient : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hphi (by exact_mod_cast Nat.totient_le d)

theorem minusOneResidue (p d : ℕ) (hd : 0 < d) (h : d ∣ p + 1) :
    Nat.ModEq d p (d - 1) := by
  apply Nat.ModEq.add_right_cancel' 1
  rw [Nat.sub_add_cancel hd]
  exact (Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl d)).symm
theorem primeReciprocalUniform : ∃ K : ℝ, 0 < K ∧
    ∀ (N d : ℕ) (P : Finset ℕ), 3 ≤ N → 0 < d →
    (∀ p ∈ P, p.Prime ∧ p ≤ N ∧ d ∣ p + 1) →
    ∑ p ∈ P, (1 : ℝ) / p ≤ K * (1 + Real.log (Real.log N)) / d.totient := by
  classical
  obtain ⟨C, hC, hBT⟩ := AmicableProgressions.brunTitchmarshUniform
  let K := 2 + 2 * C * harmonicConstant / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhc := harmonicConstant_pos
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N d P hN hd hP
  have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hlogN : 1 < Real.log (N : ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans_le (show (3 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN))
    simpa only [Real.log_exp] using hh
  have hloglog : 0 ≤ Real.log (Real.log (N : ℝ)) := (Real.log_pos hlogN).le
  have hlo := belowModulus (P.filter (· < d)) d hd (by
    intro p hp
    obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
    exact ⟨(hP p hp).1, (hP p hp).2.2, hpd⟩)
  have hhi := reciprocalAboveModulus hC hBT (P.filter (fun p => ¬ p < d)) d (d - 1) N hd
    (by omega) (by
      intro p hp
      obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
      exact ⟨(hP p hp).1, minusOneResidue p d hd (hP p hp).2.2, by omega, (hP p hp).2.1⟩)
  have hhi' := hhi.trans (mul_le_mul_of_nonneg_left (dyadicHarmonicBound N hN) (by positivity))
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => p < d) (fun p => (1 : ℝ) / p)
  calc
    _ ≤ 2 / (d.totient : ℝ) + (2 * C / ((d.totient : ℝ) * Real.log 2)) *
        (harmonicConstant * (1 + Real.log (Real.log N))) := by linarith
    _ ≤ K * (1 + Real.log (Real.log N)) / d.totient := by
      dsimp [K]
      field_simp
      nlinarith [mul_nonneg hlog2.le hloglog]

#print axioms belowModulus
#print axioms minusOneResidue
#print axioms primeReciprocalUniform
end AmicablePrimeReciprocals

