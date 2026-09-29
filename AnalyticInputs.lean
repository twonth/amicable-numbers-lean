import MertensUpper
import ZetaBounds

namespace AmicableAnalytic
open scoped BigOperators Topology
open Filter

/-- Mertens' upper bound for an arbitrary finite set of primes below y,
with an absolute constant independent of that set. -/
theorem finiteMertens : ∃ C : ℝ, ∀ (y : ℝ) (P : Finset ℕ),
    2 ≤ y → (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ y) →
      ∑ p ∈ P, (1 : ℝ) / p ≤ Real.log (Real.log y) + C := by
  obtain ⟨C, hC⟩ := AmicableMertens.sum_inv_prime_le
  refine ⟨C, ?_⟩
  intro y P hy hP
  apply le_trans _ (hC y hy)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    apply Nat.mem_primesBelow.mpr
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor (hP p hp).2), (hP p hp).1⟩
  · intro p _ _
    positivity

/-- The second prime sum in the manuscript, uniformly over its finite prime set. -/
theorem finitePrimePowersNearOne : ∀ᶠ delta : ℝ in 𝓝[>] 0,
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∑ p ∈ P, 1 / (p : ℝ) ^ (1 + delta) ≤
        Real.log (1 / delta) + Real.log 2 := by
  filter_upwards [AmicableZeta.log_zeta_near_one, self_mem_nhdsWithin] with delta hd hdpos
  intro P hP
  exact (AmicableZeta.primeSum_le_log_zeta (by simpa using hdpos) P hP).trans hd

#print axioms finiteMertens
#print axioms finitePrimePowersNearOne
end AmicableAnalytic
