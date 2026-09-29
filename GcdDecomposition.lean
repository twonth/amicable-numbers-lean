import SquarefullDecomposition
import LargeCoprimeDivisor

namespace AmicablePollack
open AmicableManuscript AmicableSquarefull
open scoped BigOperators

theorem gcdSquarefreePart {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    Nat.gcd (a * b) (sigma (a * b)) ≤ Nat.gcd a (sigma a) * b ^ 3 := by
  have hsa : 0 < sigma a := by
    rw [sigma_eq_s_add_self]; omega
  have hsb : 0 < sigma b := by
    rw [sigma_eq_s_add_self]; omega
  rw [sigma_mul hab, hab.mul_gcd]
  have h1 : Nat.gcd a (sigma a * sigma b) ≤ Nat.gcd a (sigma a) * sigma b := by
    have hh := Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ ha) (Nat.gcd_pos_of_pos_left _ ha))
      (Nat.gcd_mul_right_dvd_mul_gcd a (sigma a) (sigma b))
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.gcd_le_right a hsb))
  have h2 := Nat.gcd_le_left (sigma a * sigma b) hb
  have h3 : sigma b ≤ b ^ 2 :=
    (AmicableCoprimeDivisor.sigmaCardBound b).trans (by
      simpa [pow_two] using Nat.mul_le_mul_left b (Nat.card_divisors_le_self b))
  calc
    Nat.gcd a (sigma a * sigma b) * Nat.gcd b (sigma a * sigma b)
      ≤ (Nat.gcd a (sigma a) * sigma b) * b := Nat.mul_le_mul h1 h2
    _ ≤ (Nat.gcd a (sigma a) * b ^ 2) * b := by gcongr
    _ = _ := by ring

theorem gcdDecomposition (n : ℕ) (hn : 0 < n) {G : ℝ} (hG : 0 < G)
    (hg : G < (Nat.gcd n (sigma n) : ℝ)) :
    ∃ a b : ℕ, n = a * b ∧ Squarefree a ∧ Squarefull b ∧ a.Coprime b ∧
      (G ^ (1 / 4 : ℝ) < b ∨ G ^ (1 / 4 : ℝ) < (Nat.gcd a (sigma a) : ℝ)) := by
  obtain ⟨a, b, hnab, ha, hb, hab⟩ := squarefreeSquarefullDecomposition n hn
  refine ⟨a, b, hnab, ha, hb, hab, ?_⟩
  by_cases hbig : G ^ (1 / 4 : ℝ) < (b : ℝ)
  · exact Or.inl hbig
  right
  by_contra hsmall
  have hb0 : 0 < b := Nat.pos_of_ne_zero hb.1
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hh : (Nat.gcd n (sigma n) : ℝ) ≤ (Nat.gcd a (sigma a) : ℝ) * (b : ℝ) ^ 3 := by
    rw [hnab]
    exact_mod_cast gcdSquarefreePart ha0 hb0 hab
  have hh' : (Nat.gcd a (sigma a) : ℝ) * (b : ℝ) ^ 3 ≤
      G ^ (1 / 4 : ℝ) * (G ^ (1 / 4 : ℝ)) ^ 3 := by
    gcongr
    · exact le_of_not_gt hsmall
    · exact le_of_not_gt hbig
  have hid : G ^ (1 / 4 : ℝ) * (G ^ (1 / 4 : ℝ)) ^ 3 = G := by
    rw [← pow_succ', ← Real.rpow_mul_natCast hG.le]
    norm_num
  linarith

theorem squarefullReciprocalBound (B : Finset ℕ)
    (hB : ∀ b ∈ B, Squarefull b) :
    ∑ b ∈ B, (1 : ℝ) / b ≤ 1 + tailConstant := by
  classical
  have ht := squarefullReciprocalTail (B.erase 1) (by norm_num : (0 : ℝ) < 1) (by
    intro b hb
    obtain ⟨hb1, hbB⟩ := Finset.mem_erase.mp hb
    refine ⟨hB b hbB, ?_⟩
    have hb0 := (hB b hbB).1
    exact_mod_cast (show 1 < b by omega))
  simp only [Real.one_rpow, mul_one] at ht
  by_cases h1 : 1 ∈ B
  · rw [← Finset.add_sum_erase B (fun b => (1 : ℝ) / b) h1]
    simpa only [Nat.cast_one, div_one, one_div, add_le_add_iff_left] using ht
  · rw [Finset.erase_eq_of_notMem h1] at ht
    linarith

#print axioms gcdSquarefreePart
#print axioms gcdDecomposition
#print axioms squarefullReciprocalBound
end AmicablePollack

