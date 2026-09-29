import SieveSupport
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.GCD.BigOperators

namespace AmicableProgressions
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega
open BoundingSieve SelbergSieve

theorem countResidueError (N d a : ℕ) (hd : 0 < d) :
    |(((Finset.range N).filter (fun n => Nat.ModEq d n a)).card : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hdivlo : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  have hdivhi : (N : ℝ) / d < (N / d : ℕ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    have hh := Nat.mod_lt N hd
    have heq := Nat.div_add_mod N d
    have hh' : N < (N / d + 1) * d := by nlinarith
    exact_mod_cast hh'
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hd a]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem congruenceIntersection {d q a n : ℕ} (hc : d.Coprime q) :
    (d ∣ n ∧ Nat.ModEq q n a) ↔ Nat.ModEq (d * q) n (Nat.chineseRemainder hc 0 a) := by
  constructor
  · rintro ⟨hd, hq⟩
    exact Nat.chineseRemainder_modEq_unique hc (Nat.modEq_zero_iff_dvd.mpr hd) hq
  · intro h
    have h1 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mpr h
    refine ⟨Nat.modEq_zero_iff_dvd.mp ?_, ?_⟩
    · exact h1.1.trans (Nat.chineseRemainder hc 0 a).property.1
    · exact h1.2.trans (Nat.chineseRemainder hc 0 a).property.2

noncomputable def sievingPrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).filter (fun p => ¬p ∣ q)

noncomputable def primeProduct (q : ℕ) (z : ℝ) : ℕ := ∏ p ∈ sievingPrimes q z, p

theorem primeProductSquarefree (q : ℕ) (z : ℝ) : Squarefree (primeProduct q z) := by
  apply (squarefree_primorial ⌊z⌋₊).squarefree_of_dvd
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem primeProductCoprime (q : ℕ) (z : ℝ) : (primeProduct q z).Coprime q := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  obtain ⟨hpP, hpq⟩ := Finset.mem_filter.mp hp
  exact (Nat.prime_of_mem_primesLE hpP).coprime_iff_not_dvd.mpr hpq

noncomputable def progressionSieve (N q a : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range N).filter (fun n => Nat.ModEq q n a)
  prodPrimes := primeProduct q z
  prodPrimes_squarefree := primeProductSquarefree q z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (N : ℝ) / q
  nu := (ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply_ne hp.ne_zero,
      Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hp.ne_zero, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  level := z
  one_le_level := hz

theorem progressionRemainder (N q a : ℕ) (z : ℝ) (hz : 1 ≤ z) (hq : 0 < q)
    {d : ℕ} (hd : d ∣ primeProduct q z) :
    |(progressionSieve N q a z hz).rem d| ≤ 1 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (primeProductSquarefree q z).ne_zero.bot_lt
  have hc : d.Coprime q := (primeProductCoprime q z).of_dvd_left hd
  let v := Nat.chineseRemainder hc 0 a
  have hmult : (progressionSieve N q a z hz).multSum d =
      (((Finset.range N).filter (fun n => Nat.ModEq (d * q) n v)).card : ℝ) := by
    simp only [multSum, progressionSieve]
    rw [← Finset.sum_filter, Finset.filter_filter]
    have hset : ((Finset.range N).filter (fun n => Nat.ModEq q n a ∧ d ∣ n)) =
        (Finset.range N).filter (fun n => Nat.ModEq (d * q) n v) := by
      ext n
      simp only [Finset.mem_filter]
      rw [(and_comm : Nat.ModEq q n a ∧ d ∣ n ↔ d ∣ n ∧ Nat.ModEq q n a), congruenceIntersection hc]
    rw [hset]
    simp
  have hh := countResidueError N (d * q) v (mul_pos hd0 hq)
  rw [rem, hmult]
  have hnu : (progressionSieve N q a z hz).nu d = (1 : ℝ) / d := by
    simp [progressionSieve, ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply_ne hd0.ne']
  rw [hnu]
  change |(_ : ℝ) - (1 / d) * ((N : ℝ) / q)| ≤ 1
  convert hh using 2 <;> push_cast <;> ring

theorem progressionDenominator (N q a : ℕ) (z : ℝ) (hz : 1 ≤ z) (hq : 0 < q) :
    (q.totient : ℝ) / q * (Real.log z / 2) ≤
      (progressionSieve N q a z hz).selbergBoundingSum := by
  apply AmicableSieve.sieveDenominatorCoprime (progressionSieve N q a z hz) q hq rfl
  intro p hp hpz hpq
  change p ∣ ∏ r ∈ sievingPrimes q z, r
  apply Finset.dvd_prod_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨?_, hpq⟩
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by linarith)).mpr hpz, hp⟩

theorem progressionErrorSum (N q a : ℕ) (z : ℝ) (hz : 1 ≤ z) (hq : 0 < q) :
    ∑ d ∈ (primeProduct q z).divisors,
      (if (d : ℝ) ≤ z then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
        |(progressionSieve N q a z hz).rem d| else 0) ≤ z * (1 + Real.log z) ^ 3 := by
  calc
    _ ≤ ∑ d ∈ (primeProduct q z).divisors,
        if (d : ℝ) ≤ z then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact mul_le_of_le_one_right (by positivity)
          (progressionRemainder N q a z hz hq (Nat.dvd_of_mem_divisors hd))
      · rfl
    _ ≤ _ := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow z hz (primeProductSquarefree q z)

theorem progressionSiftedBound (N q a : ℕ) (z : ℝ) (hz : 1 < z) (hq : 0 < q) :
    (progressionSieve N q a z hz.le).siftedSum ≤
      2 * N / ((q.totient : ℝ) * Real.log z) + z * (1 + Real.log z) ^ 3 := by
  have hden := progressionDenominator N q a z hz.le hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hlower : 0 < (q.totient : ℝ) / q * (Real.log z / 2) := by positivity
  have hmain : ((N : ℝ) / q) / (progressionSieve N q a z hz.le).selbergBoundingSum ≤
      2 * N / ((q.totient : ℝ) * Real.log z) := by
    calc
      _ ≤ ((N : ℝ) / q) / ((q.totient : ℝ) / q * (Real.log z / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hlower hden
      _ = _ := by field_simp
  exact (SelbergSieve.selberg_bound_simple (progressionSieve N q a z hz.le)).trans
    (add_le_add hmain (progressionErrorSum N q a z hz.le hq))

theorem primeDivisorProductSmall {q p : ℕ} {z : ℝ} (hp : p.Prime)
    (hpd : p ∣ primeProduct q z) : p ≤ ⌊z⌋₊ := by
  have hm : p ∈ (primeProduct q z).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, hpd, (primeProductSquarefree q z).ne_zero⟩
  have hprod : (primeProduct q z).primeFactors = sievingPrimes q z :=
    Nat.primeFactors_prod (fun r hr => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hr).1)
  rw [hprod] at hm
  exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hm).1).1

noncomputable def primeCount (N q a : ℕ) : ℕ :=
  (((Finset.range N).filter (fun n => Nat.ModEq q n a)).filter Nat.Prime).card

theorem progressionPrimeBound (N q a : ℕ) (z : ℝ) (hz : 1 < z) (hq : 0 < q) :
    (primeCount N q a : ℝ) ≤
      2 * N / ((q.totient : ℝ) * Real.log z) + 3 * z * (1 + Real.log z) ^ 3 := by
  classical
  let A := (Finset.range N).filter (fun n => Nat.ModEq q n a)
  let C := A.filter (fun n => (primeProduct q z).Coprime n)
  have hsub : A.filter Nat.Prime ⊆ C ∪ Finset.range (⌊z⌋₊ + 1) := by
    intro p hp
    obtain ⟨hpA, hprime⟩ := Finset.mem_filter.mp hp
    by_cases hpd : p ∣ primeProduct q z
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (primeDivisorProductSmall hprime hpd)))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hpA, (hprime.coprime_iff_not_dvd.mpr hpd).symm⟩)
  have hcard : primeCount N q a ≤ C.card + (⌊z⌋₊ + 1) := by
    exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_union_le C (Finset.range (⌊z⌋₊ + 1)))
  have hsift : (C.card : ℝ) = (progressionSieve N q a z hz.le).siftedSum := by
    change (C.card : ℝ) = ∑ n ∈ A, if (primeProduct q z).Coprime n then (1 : ℝ) else 0
    rw [← Finset.sum_filter]
    simp [C]
  have hz0 : 0 ≤ z := by linarith
  have hsmall : (⌊z⌋₊ : ℝ) + 1 ≤ 2 * z := by linarith [Nat.floor_le hz0]
  have hpow : 1 ≤ (1 + Real.log z) ^ 3 := one_le_pow₀ (by linarith [Real.log_pos hz])
  have herr : 2 * z ≤ 2 * z * (1 + Real.log z) ^ 3 := le_mul_of_one_le_right (by positivity) hpow
  have hcast : (primeCount N q a : ℝ) ≤ C.card + ((⌊z⌋₊ : ℝ) + 1) := by exact_mod_cast hcard
  rw [hsift] at hcast
  have hb := progressionSiftedBound N q a z hz hq
  linarith

#print axioms primeDivisorProductSmall
#print axioms progressionPrimeBound
#print axioms progressionErrorSum
#print axioms progressionSiftedBound
#print axioms progressionRemainder
#print axioms progressionDenominator
#print axioms countResidueError
#print axioms congruenceIntersection
#print axioms primeProductSquarefree
#print axioms primeProductCoprime
end AmicableProgressions




