import MomentWeight
import GeometricBounds
import AnalyticInputs

namespace AmicableMoment
open scoped BigOperators Topology
open Filter

noncomputable def theta : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
noncomputable def quadraticConstant : ℝ :=
  (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / (1 - theta)

theorem exactEulerProduct {y eta delta : ℝ} (hy : 0 < y)
    (hs : Summable (term y eta delta)) :
    ∏' p : Nat.Primes, (1 - term y eta delta p)⁻¹ =
      ∑' n : ℕ, term y eta delta n := by
  have hn : Summable (fun n => ‖term y eta delta n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (term_nonneg hy eta delta _)] using hs
  exact EulerProduct.eulerProduct_completely_multiplicative_tprod
    (f := termHom hy eta delta) hn

theorem theta_lt_one : theta < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem prefixGeometricBound (f : ℕ →* ℝ) (hf : ∀ n, 0 ≤ f n)
    (hp : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n ≤
      ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := by
  classical
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp
    (N + 1)).2
  have hmem : ∀ n ∈ Finset.Icc 1 N, n ∈ (N + 1).smoothNumbers := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  rw [← Finset.sum_subtype_of_mem f hmem]
  exact sum_le_hasSum _ (fun n _ => hf n) hsum

theorem primeTermSumBound {y eta delta : ℝ} (hy : 0 < y)
    (he0 : 0 ≤ eta) (hd : 0 ≤ delta)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (C D : ℝ)
    (hsmall : ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ y), (1 : ℝ) / p ≤ C)
    (hlarge : ∑ p ∈ P.filter (fun p : ℕ => y < (p : ℝ)),
        1 / (p : ℝ) ^ (1 + delta) ≤ D) :
    ∑ p ∈ P, term y eta delta p ≤ y ^ eta * (C + D) := by
  classical
  have hsplit : ∑ p ∈ P, term y eta delta p =
      (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ y), term y eta delta p) +
      ∑ p ∈ P.filter (fun p : ℕ => y < (p : ℝ)), term y eta delta p := by
    simpa using (Finset.sum_filter_add_sum_filter_not P
      (fun p : ℕ => (p : ℝ) ≤ y) (fun p => term y eta delta p)).symm
  rw [hsplit, mul_add]
  apply add_le_add
  · calc
      _ ≤ ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ y), y ^ eta / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact term_prime_le_y_rpow_div hy he0 hd (hP p (Finset.mem_filter.mp hp).1)
      _ = y ^ eta * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ y), (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hy.le _)
  · calc
      _ ≤ ∑ p ∈ P.filter (fun p : ℕ => y < (p : ℝ)), y ^ eta / (p : ℝ) ^ (1 + delta) := by
        apply Finset.sum_le_sum
        intro p hp
        exact term_prime_le_y_rpow hy he0 (hP p (Finset.mem_filter.mp hp).1)
      _ = y ^ eta * ∑ p ∈ P.filter (fun p : ℕ => y < (p : ℝ)),
          (1 : ℝ) / (p : ℝ) ^ (1 + delta) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hy.le _)

theorem uniformPrefixMomentBound : ∃ C : ℝ,
    ∀ᶠ delta : ℝ in 𝓝[>] 0, ∀ y eta : ℝ,
      2 ≤ y → 0 ≤ eta → eta ≤ 1 / 4 → ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, term y eta delta n ≤
        Real.exp (y ^ eta * (Real.log (Real.log y) + C +
          Real.log (1 / delta) + Real.log 2) + quadraticConstant) := by
  obtain ⟨C, hC⟩ := AmicableAnalytic.finiteMertens
  refine ⟨C, ?_⟩
  filter_upwards [AmicableAnalytic.finitePrimePowersNearOne, self_mem_nhdsWithin]
    with delta hd hdpos
  intro y eta hy he0 he N
  have hypos : 0 < y := by linarith
  have hdelta : 0 ≤ delta := le_of_lt hdpos
  let P := (N + 1).primesBelow
  have hP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hsmall := hC y (P.filter (fun p : ℕ => (p : ℝ) ≤ y)) hy (by
    intro p hp
    obtain ⟨hpP, hpy⟩ := Finset.mem_filter.mp hp
    exact ⟨hP p hpP, hpy⟩)
  have hlarge := hd (P.filter (fun p : ℕ => y < (p : ℝ))) (by
    intro p hp
    exact hP p (Finset.mem_filter.mp hp).1)
  have hlinear := primeTermSumBound hypos he0 hdelta P hP
    (Real.log (Real.log y) + C) (Real.log (1 / delta) + Real.log 2) hsmall hlarge
  have hquad := primeTermSquareSumBound hypos he0 he hdelta P hP
  have hgeom := AmicableGeometric.finiteGeometricBound P (term y eta delta)
    theta (y ^ eta * ((Real.log (Real.log y) + C) + (Real.log (1 / delta) + Real.log 2)))
    (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) theta_lt_one
    (fun p hp => ⟨term_nonneg hypos eta delta p,
      primeTermUniformLtOne hypos he0 he hdelta (hP p hp)⟩) hlinear hquad
  have hprefix := prefixGeometricBound (termHom hypos eta delta).toMonoidHom
    (term_nonneg hypos eta delta) (fun {p} hp => term_prime_lt_one hypos he0 he hdelta hp) N
  exact hprefix.trans (by simpa [P, termHom, quadraticConstant, add_assoc] using hgeom)

theorem uniformMomentBound : ∃ C : ℝ,
    ∀ᶠ delta : ℝ in 𝓝[>] 0, ∀ y eta : ℝ,
      2 ≤ y → 0 ≤ eta → eta ≤ 1 / 4 →
      Summable (term y eta delta) ∧
      (∑' n : ℕ, term y eta delta n) ≤
        Real.exp (y ^ eta * (Real.log (Real.log y) + C +
          Real.log (1 / delta) + Real.log 2) + quadraticConstant) := by
  obtain ⟨C, hC⟩ := uniformPrefixMomentBound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with delta hd
  intro y eta hy he0 he
  have hypos : 0 < y := by linarith
  have hprefix := hd y eta hy he0 he
  have hrange : ∀ N : ℕ, ∑ n ∈ Finset.range N, term y eta delta n ≤
      Real.exp (y ^ eta * (Real.log (Real.log y) + C +
        Real.log (1 / delta) + Real.log 2) + quadraticConstant) := by
    intro N
    by_cases hN : N = 0
    · simp [hN]
      positivity
    rw [Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hN), term_zero, zero_add]
    apply le_trans _ (hprefix N)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      exact Finset.mem_Icc.mpr ⟨hn1, hnN.le⟩
    · intro n _ _
      exact term_nonneg hypos eta delta n
  exact ⟨summable_of_sum_range_le (term_nonneg hypos eta delta) hrange,
    Real.tsum_le_of_sum_range_le (term_nonneg hypos eta delta) hrange⟩

theorem primeShiftBound {y eta delta : ℝ} (hy : 0 < y) (hd : 0 ≤ delta)
    (hsum : Summable (term y eta delta)) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) :
    ∑ q ∈ P, AmicableWeight.H y (q + 1) ^ eta / (q : ℝ) ^ (1 + delta) ≤
      (2 : ℝ) ^ (1 + delta) * ∑' n : ℕ, term y eta delta n := by
  have heach : ∀ q ∈ P,
      AmicableWeight.H y (q + 1) ^ eta / (q : ℝ) ^ (1 + delta) ≤
        (2 : ℝ) ^ (1 + delta) * term y eta delta (q + 1) := by
    intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (hP q hq).pos
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (hP q hq).one_le
    have hqpow : 0 < (q : ℝ) ^ (1 + delta) := Real.rpow_pos_of_pos hqpos _
    have hqspow : 0 < ((q + 1 : ℕ) : ℝ) ^ (1 + delta) := by positivity
    have hpow : ((q + 1 : ℕ) : ℝ) ^ (1 + delta) ≤
        (2 : ℝ) ^ (1 + delta) * (q : ℝ) ^ (1 + delta) := by
      rw [← Real.mul_rpow (by norm_num) hqpos.le]
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      push_cast
      linarith
    rw [term_of_pos y eta delta (Nat.succ_pos q), ← mul_div_assoc]
    apply (div_le_div_iff₀ hqpow hqspow).mpr
    have hH : 0 ≤ AmicableWeight.H y (q + 1) ^ eta :=
      Real.rpow_nonneg (AmicableWeight.H_pos hy _).le _
    nlinarith [mul_le_mul_of_nonneg_left hpow hH]
  calc
    _ ≤ ∑ q ∈ P, (2 : ℝ) ^ (1 + delta) * term y eta delta (q + 1) :=
      Finset.sum_le_sum heach
    _ = (2 : ℝ) ^ (1 + delta) * ∑ q ∈ P, term y eta delta (q + 1) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hi : Set.InjOn (fun q : ℕ => q + 1) (↑P : Set ℕ) := by
        intro a _ b _ hab
        change a + 1 = b + 1 at hab
        omega
      rw [← Finset.sum_image hi]
      exact hsum.sum_le_tsum _ (fun n _ => term_nonneg hy eta delta n)

#print axioms prefixGeometricBound
#print axioms primeTermSumBound
#print axioms theta_lt_one
#print axioms uniformPrefixMomentBound
#print axioms uniformMomentBound
#print axioms primeShiftBound
end AmicableMoment
