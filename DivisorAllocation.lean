import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace AmicableAllocation
open scoped BigOperators

/-- Distribute a divisor of a finite product among its factors. The distributed
factors need not be coprime, and factors equal to one are allowed. -/
theorem distributeDivisor {ι : Type*} (I : Finset ι) (f : ι → ℕ) {d : ℕ}
    (hd : d ∣ ∏ i ∈ I, f i) :
    ∃ e : ι → ℕ, (∀ i ∈ I, e i ∣ f i) ∧ ∏ i ∈ I, e i = d := by
  classical
  induction I using Finset.induction_on generalizing d with
  | empty =>
    have hd1 : d = 1 := Nat.dvd_one.mp (by simpa using hd)
    exact ⟨fun _ => 1, by simp, by simp [hd1]⟩
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi] at hd
    obtain ⟨d₁, d₂, hd₁, hd₂, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨e, he, heprod⟩ := ih hd₂
    refine ⟨Function.update e i d₁, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hd₁
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using he j hj
    · rw [Finset.prod_insert hi, Function.update_self]
      have hprod : ∏ j ∈ I, Function.update e i d₁ j = ∏ j ∈ I, e j := by
        apply Finset.prod_congr rfl
        intro j hj
        exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
      rw [hprod, heprod]
      exact heq.symm

/-- Removing the gcd with one factor leaves a divisor of the other factor. -/
theorem quotientGcdDivides {a b c : ℕ} (ha : 0 < a) (hd : a ∣ b * c) :
    a / Nat.gcd a b ∣ c := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hac : (a / Nat.gcd a b).Coprime (b / Nat.gcd a b) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hdiv : a / Nat.gcd a b ∣ (b / Nat.gcd a b) * c := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      Nat.gcd a b * ((b / Nat.gcd a b) * c) = b * c := by
        rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
      _ = a * k := hk
      _ = Nat.gcd a b * ((a / Nat.gcd a b) * k) := by
        rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)]
  exact hac.dvd_of_dvd_mul_left hdiv

#print axioms distributeDivisor
#print axioms quotientGcdDivides
end AmicableAllocation
