import SquarefullDecomposition
import ManuscriptArithmetic

namespace AmicableStructure
open AmicableManuscript AmicableSquarefull

/-- The manuscript's squarefree unitary factor, after removing shared primes. -/
theorem structuralFactorization {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    ∃ a B b : ℕ, n = B * a ∧ Squarefree a ∧ a.Coprime B ∧ a.Coprime n' ∧
      Squarefull b ∧ b ∣ n ∧ B ≤ b * Nat.gcd n n' := by
  obtain ⟨a0, b, hnab, ha0, hb, hab⟩ := squarefreeSquarefullDecomposition n hn
  let c := Nat.gcd a0 n'
  let a := a0 / c
  have hca : c ∣ a0 := Nat.gcd_dvd_left _ _
  have hac : a * c = a0 := Nat.div_mul_cancel hca
  have had : a ∣ a0 := Nat.div_dvd_of_dvd hca
  have ha : Squarefree a := ha0.squarefree_of_dvd had
  have hacop : a.Coprime c := Nat.coprime_of_squarefree_mul (hac ▸ ha0)
  have habcop : a.Coprime b := hab.of_dvd_left had
  refine ⟨a, b * c, b, ?_, ha, habcop.mul_right hacop, ?_, hb, ?_, ?_⟩
  · rw [hnab, ← hac]; ring
  · exact Nat.coprime_div_gcd_of_squarefree ha0 hn'.ne'
  · rw [hnab]; exact dvd_mul_left _ _
  · apply Nat.mul_le_mul_left
    apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn)
    apply Nat.dvd_gcd
    · exact hca.trans (hnab ▸ dvd_mul_right _ _)
    · exact Nat.gcd_dvd_right _ _

theorem boundedStructuralFactorization {n n' : ℕ} {H G : ℝ}
    (hn : 0 < n) (hn' : 0 < n')
    (hfull : ∀ b : ℕ, Squarefull b → b ∣ n → (b : ℝ) ≤ H)
    (hg : (Nat.gcd n n' : ℝ) ≤ G) :
    ∃ a B : ℕ, n = B * a ∧ Squarefree a ∧ a.Coprime B ∧ a.Coprime n' ∧
      (B : ℝ) ≤ H * G := by
  obtain ⟨a, B, b, hnB, ha, hab, han', hb, hbn, hB⟩ := structuralFactorization hn hn'
  refine ⟨a, B, hnB, ha, hab, han', ?_⟩
  have hcast : (B : ℝ) ≤ (b : ℝ) * (Nat.gcd n n' : ℝ) := by exact_mod_cast hB
  exact hcast.trans (mul_le_mul (hfull b hb hbn) hg (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) (hfull b hb hbn)))

/-- Involutivity converts a bound for exceptional members into a bound for pairs. -/
theorem amicablePartnerInjective (F : Finset ℕ)
    (hF : ∀ n ∈ F, ∃ n', Amicable n n') : Set.InjOn s F := by
  intro n hn m hm heq
  obtain ⟨n', hn'⟩ := hF n hn
  obtain ⟨m', hm'⟩ := hF m hm
  have hsn : s (s n) = n := by rw [hn'.2.2.2.1]; exact hn'.2.2.2.2
  have hsm : s (s m) = m := by rw [hm'.2.2.2.1]; exact hm'.2.2.2.2
  rw [← hsn, heq, hsm]

#print axioms structuralFactorization
#print axioms boundedStructuralFactorization
#print axioms amicablePartnerInjective
end AmicableStructure
