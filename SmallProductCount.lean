import CountFibres
import PartialSummation

namespace AmicableStructure
open AmicableManuscript
open scoped BigOperators

theorem smallProductCount (F : Finset ℕ) (m m' : ℕ → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ n ∈ F, 0 < m n ∧ 0 < m' n)
    (hprod : ∀ n ∈ F, (m n : ℝ) * m' n ≤ T)
    (huniq : ∀ n1 ∈ F, ∀ n2 ∈ F, m n1 = m n2 → m' n1 = m' n2 → n1 = n2) :
    (F.card : ℝ) ≤ 2 * T * (⌊Real.log ⌊T⌋₊ / Real.log 2⌋₊ + 1 : ℕ) := by
  classical
  let I := Finset.Icc 1 ⌊T⌋₊
  have hmap : ∀ n ∈ F, m n ∈ I := by
    intro n hn
    have hmn : (m n : ℝ) ≤ T := by
      have hm' : (1 : ℝ) ≤ m' n := by exact_mod_cast (hpos n hn).2
      have hh := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (m n))
      nlinarith [hprod n hn]
    exact Finset.mem_Icc.mpr ⟨(hpos n hn).1, Nat.le_floor hmn⟩
  have hfibre : ∀ j ∈ I, ((F.filter (fun n => m n = j)).card : ℝ) ≤ T / j := by
    intro j hj
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    let B := F.filter (fun n => m n = j)
    have hinj : Set.InjOn m' B := by
      intro n1 hn1 n2 hn2 heq
      obtain ⟨hn1F,hm1⟩ := Finset.mem_filter.mp hn1
      obtain ⟨hn2F,hm2⟩ := Finset.mem_filter.mp hn2
      exact huniq n1 hn1F n2 hn2F (hm1.trans hm2.symm) heq
    have hsub : B.image m' ⊆ Finset.Icc 1 ⌊T / j⌋₊ := by
      intro k hk
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hnF,hmj⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_Icc.mpr ⟨(hpos n hnF).2, Nat.le_floor ?_⟩
      apply (le_div_iff₀ (by exact_mod_cast hjpos : (0 : ℝ) < j)).mpr
      have hh := hprod n hnF
      rw [hmj] at hh
      nlinarith
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at hh
    simpa using (Nat.cast_le.mpr hh : (B.card : ℝ) ≤ (Finset.Icc 1 ⌊T / j⌋₊).card) |>.trans
      (by simpa using Nat.floor_le (div_nonneg hT (Nat.cast_nonneg j)))
  have hrec := AmicablePartialSummation.reciprocalFromCount I ⌊T⌋₊ 1 (by norm_num)
    (fun j hj => ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2⟩) (by
      intro Z hZ
      have hsub : I.filter (· ≤ Z) ⊆ Finset.Icc 1 Z := by
        intro j hj
        obtain ⟨hjI,hjZ⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hjI).1,hjZ⟩
      have hh := Finset.card_le_card hsub
      simpa using (Nat.cast_le.mpr hh : ((I.filter (· ≤ Z)).card : ℝ) ≤ (Finset.Icc 1 Z).card))
  have hsum := Finset.sum_fiberwise_of_maps_to hmap (fun _ : ℕ => (1 : ℝ))
  calc
    (F.card : ℝ) = ∑ j ∈ I, ((F.filter (fun n => m n = j)).card : ℝ) := by simpa using hsum.symm
    _ ≤ ∑ j ∈ I, T / j := Finset.sum_le_sum hfibre
    _ = T * ∑ j ∈ I, (1 : ℝ) / j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := by have hh := mul_le_mul_of_nonneg_left hrec hT; nlinarith

theorem pairPrimeReconstruction {m m' p1 p2 q1 q2 : ℕ}
    (hm : 0 < m) (hp1 : p1.Prime) (hp2 : p2.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime)
    (hpm1 : p1.Coprime m) (hpm2 : p2.Coprime m)
    (hqm1 : q1.Coprime m') (hqm2 : q2.Coprime m')
    (h1 : Amicable (p1 * m) (q1 * m')) (h2 : Amicable (p2 * m) (q2 * m')) : p1 = p2 := by
  have he11 := h1.2.2.2.1
  have he12 := h1.2.2.2.2
  have he21 := h2.2.2.2.1
  have he22 := h2.2.2.2.2
  rw [s_mul_prime hp1 hpm1] at he11
  rw [s_mul_prime hq1 hqm1] at he12
  rw [s_mul_prime hp2 hpm2] at he21
  rw [s_mul_prime hq2 hqm2] at he22
  have hsig : 0 < sigma m := by rw [sigma_eq_s_add_self]; omega
  have he1 : (q1 : ℤ) * ((m : ℤ) * m' - (s m : ℤ) * s m') =
      (m : ℤ) * sigma m + (s m : ℤ) * sigma m' :=
    AmicableAudit.eliminatePrime m m' p1 q1 (s m) (s m') (sigma m) (sigma m')
      (by exact_mod_cast (show m' * q1 = p1 * s m + sigma m by nlinarith))
      (by exact_mod_cast (show m * p1 = q1 * s m' + sigma m' by nlinarith))
  have he2 : (q2 : ℤ) * ((m : ℤ) * m' - (s m : ℤ) * s m') =
      (m : ℤ) * sigma m + (s m : ℤ) * sigma m' :=
    AmicableAudit.eliminatePrime m m' p2 q2 (s m) (s m') (sigma m) (sigma m')
      (by exact_mod_cast (show m' * q2 = p2 * s m + sigma m by nlinarith))
      (by exact_mod_cast (show m * p2 = q2 * s m' + sigma m' by nlinarith))
  have hpositive : (0 : ℤ) < (m : ℤ) * sigma m + (s m : ℤ) * sigma m' := by positivity
  have hcoef : (m : ℤ) * m' - (s m : ℤ) * s m' ≠ 0 := by
    intro hh
    rw [hh,mul_zero] at he1
    omega
  have hqeq : q1 = q2 := by
    exact_mod_cast (mul_right_cancel₀ hcoef (he1.trans he2.symm))
  rw [hqeq] at he12
  nlinarith

#print axioms smallProductCount
#print axioms pairPrimeReconstruction
end AmicableStructure
