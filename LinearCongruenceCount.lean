import ResidueCounting
import Mathlib.Data.Nat.ModEq

namespace AmicableResidues
open AmicableManuscript
open scoped BigOperators

theorem linearCongruenceCount (F : Finset ℕ) {q c a : ℕ} {T : ℝ}
    (hq : 0 < q) (hT : 0 ≤ T)
    (hF : ∀ n ∈ F, (n : ℝ) ≤ T ∧ Nat.ModEq q (c * n) a) :
    (F.card : ℝ) ≤ 1 + T * (Nat.gcd q c : ℝ) / q := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨n0, hn0⟩ := hne
    let g := Nat.gcd q c
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hq
    have hgd : g ∣ q := Nat.gcd_dvd_left _ _
    have hquot : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgd) hg
    have hh := oneResidueRealBound F hquot hT (by
      intro n hn
      refine ⟨(hF n hn).1, ?_⟩
      exact ((hF n hn).2.trans (hF n0 hn0).2.symm).cancel_left_div_gcd hq)
    have hcast : ((q / g : ℕ) : ℝ) = (q : ℝ) / g := Nat.cast_div hgd (by exact_mod_cast hg.ne')
    have hid : T / ((q / g : ℕ) : ℝ) = T * (g : ℝ) / q := by rw [hcast, div_div_eq_mul_div]
    simpa only [hid] using hh
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

theorem structuralCongruenceCount (F : Finset ℕ) (D m : ℕ) {X : ℝ}
    (hD : 0 < D) (hm : 0 < m) (hX : 0 ≤ X) (hcop : D.Coprime (AmicableManuscript.sigma D))
    (hF : ∀ M ∈ F, (M : ℝ) ≤ X / D ∧
      Nat.ModEq (AmicableManuscript.sigma D) (AmicableManuscript.sigma m * D * M)
        (m * AmicableManuscript.sigma m)) :
    (F.card : ℝ) ≤ 1 + X * AmicableManuscript.sigma m / (D : ℝ) ^ 2 := by
  have hsd : D ≤ sigma D := by rw [sigma_eq_s_add_self]; omega
  have hsm : m ≤ AmicableManuscript.sigma m := by rw [AmicableManuscript.sigma_eq_s_add_self]; omega
  have hsigD : 0 < AmicableManuscript.sigma D := hD.trans_le hsd
  have hsigm : 0 < AmicableManuscript.sigma m := hm.trans_le hsm
  have hh := linearCongruenceCount F hsigD (div_nonneg hX (Nat.cast_nonneg D)) hF
  have hg : Nat.gcd (AmicableManuscript.sigma D) (AmicableManuscript.sigma m * D) =
      Nat.gcd (AmicableManuscript.sigma D) (AmicableManuscript.sigma m) :=
    hcop.gcd_mul_right_cancel_right _
  rw [hg] at hh
  have hgl : (Nat.gcd (AmicableManuscript.sigma D) (AmicableManuscript.sigma m) : ℝ) ≤
      AmicableManuscript.sigma m := by exact_mod_cast Nat.gcd_le_right _ hsigm
  have hDsig : (D : ℝ) ≤ AmicableManuscript.sigma D := by exact_mod_cast hsd
  have hfrac : X / (D : ℝ) * Nat.gcd (AmicableManuscript.sigma D) (AmicableManuscript.sigma m) /
      AmicableManuscript.sigma D ≤ X * AmicableManuscript.sigma m / (D : ℝ) ^ 2 := by
    calc
      _ ≤ (X / (D : ℝ) * AmicableManuscript.sigma m) / AmicableManuscript.sigma D := by gcongr
      _ ≤ (X / (D : ℝ) * AmicableManuscript.sigma m) / D := by gcongr
      _ = _ := by ring
  linarith

#print axioms linearCongruenceCount
#print axioms structuralCongruenceCount
end AmicableResidues



