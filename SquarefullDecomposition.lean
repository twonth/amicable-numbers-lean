import Squarefull
import Mathlib.Data.Nat.Factorization.Induction

namespace AmicableSquarefull

 theorem squarefullMul {a b : ℕ} (ha : Squarefull a) (hb : Squarefull b) : Squarefull (a * b) := by
  refine ⟨Nat.mul_ne_zero ha.1 hb.1, ?_⟩
  intro p hp
  rw [Nat.factorization_mul ha.1 hb.1, Finsupp.add_apply]
  rw [Nat.primeFactors_mul ha.1 hb.1] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have := ha.2 p hp; omega
  · have := hb.2 p hp; omega

theorem squarefullPrimePower {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) : Squarefull (p ^ e) := by
  refine ⟨pow_ne_zero _ hp.ne_zero, ?_⟩
  intro q hq
  rw [Nat.primeFactors_prime_pow (by omega : e ≠ 0) hp, Finset.mem_singleton] at hq
  subst q
  simpa [hp.factorization_pow] using he

theorem squarefullOne : Squarefull 1 := by simp [Squarefull]

theorem squarefreeSquarefullDecomposition (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, n = a * b ∧ Squarefree a ∧ Squarefull b ∧ a.Coprime b := by
  have hall : ∀ n : ℕ, 0 < n → ∃ a b : ℕ, n = a * b ∧ Squarefree a ∧ Squarefull b ∧ a.Coprime b := by
    apply Nat.recOnPrimePow
    · intro h; omega
    · intro _; exact ⟨1, 1, by norm_num, squarefree_one, squarefullOne, Nat.coprime_one_left 1⟩
    · intro m p e hp hpm he ih hpos
      have hmpos : 0 < m := by
        by_contra h
        have hm : m = 0 := by omega
        simp [hm] at hpos
      obtain ⟨a, b, hm, ha, hb, hab⟩ := ih hmpos
      have hpc : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm
      rw [hm, Nat.coprime_mul_iff_right] at hpc
      by_cases he1 : e = 1
      · subst e
        refine ⟨p * a, b, ?_, ?_, hb, ?_⟩
        · simp [hm, mul_assoc]
        · exact (Nat.squarefree_mul hpc.1).mpr ⟨hp.squarefree, ha⟩
        · exact hpc.2.mul_left hab
      · refine ⟨a, p ^ e * b, ?_, ha, squarefullMul (squarefullPrimePower hp (by omega)) hb, ?_⟩
        · simp [hm]; ring
        · exact hpc.1.symm.pow_right e |>.mul_right hab
  exact hall n hn

#print axioms squarefullMul
#print axioms squarefullPrimePower
#print axioms squarefreeSquarefullDecomposition
end AmicableSquarefull
