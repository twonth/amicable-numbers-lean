import ManuscriptArithmetic

namespace AmicableResidues
open scoped BigOperators

theorem oneResidueCard (B : Finset ℕ) (N d a : ℕ)
    (hB : ∀ n ∈ B, n ≤ N ∧ n % d = a) : B.card ≤ N / d + 1 := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => n / d) B := by
    intro n hn m hm hnm
    have hnmod := (hB n hn).2
    have hmmod := (hB m hm).2
    have h1 := Nat.mod_add_div n d
    have h2 := Nat.mod_add_div m d
    change n / d = m / d at hnm
    rw [hnmod, hnm] at h1
    rw [hmmod] at h2
    omega
  calc
    B.card = (B.image (fun n => n / d)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / d + 1)).card := Finset.card_le_card (by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hB n hn).1)))
    _ = N / d + 1 := Finset.card_range _

theorem oneResidueRealBound (B : Finset ℕ) {T : ℝ} {d a : ℕ}
    (hd : 0 < d) (hT : 0 ≤ T)
    (hB : ∀ n ∈ B, (n : ℝ) ≤ T ∧ n % d = a) :
    (B.card : ℝ) ≤ 1 + T / d := by
  have hh := oneResidueCard B ⌊T⌋₊ d a (fun n hn =>
    ⟨(Nat.le_floor_iff hT).mpr (hB n hn).1, (hB n hn).2⟩)
  have hdiv : ((⌊T⌋₊ / d : ℕ) : ℝ) ≤ T / d := by
    apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    have hh : (⌊T⌋₊ / d) * d ≤ ⌊T⌋₊ := Nat.div_mul_le_self _ _
    exact (by exact_mod_cast hh : (⌊T⌋₊ / d : ℕ) * (d : ℝ) ≤ ⌊T⌋₊).trans (Nat.floor_le hT)
  have hcast : (B.card : ℝ) ≤ (⌊T⌋₊ / d : ℕ) + 1 := by exact_mod_cast hh
  linarith

theorem oneResidueBelowModulus (B : Finset ℕ) {d a : ℕ}
    (hB : ∀ n ∈ B, n < d ∧ n % d = a) : B.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have hn' := (hB n hn).2
  have hm' := (hB m hm).2
  rw [Nat.mod_eq_of_lt (hB n hn).1] at hn'
  rw [Nat.mod_eq_of_lt (hB m hm).1] at hm'
  exact hn'.trans hm'.symm

#print axioms oneResidueCard
#print axioms oneResidueRealBound
#print axioms oneResidueBelowModulus
end AmicableResidues

