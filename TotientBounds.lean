import ManuscriptArithmetic

namespace AmicableTotient
open scoped BigOperators

theorem primeHalf {p : ℕ} (hp : p.Prime) : p ≤ 2 * p.totient := by
  rw [Nat.totient_prime hp]
  have := hp.two_le
  omega

theorem primeListHalf (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) :
    l.prod ≤ 2 ^ l.length * l.prod.totient := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have htail := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.prod_cons, List.length_cons]
    calc
      p * l.prod ≤ (2 * p.totient) * (2 ^ l.length * l.prod.totient) :=
        Nat.mul_le_mul (primeHalf hp) htail
      _ = 2 ^ (l.length + 1) * (p.totient * l.prod.totient) := by ring
      _ ≤ 2 ^ (l.length + 1) * (p * l.prod).totient :=
        Nat.mul_le_mul_left _ (Nat.totient_super_multiplicative p l.prod)

theorem totientHalf (n : ℕ) : n ≤ 2 ^ (ArithmeticFunction.cardFactors n) * n.totient := by
  by_cases hn : n = 0
  · simp [hn]
  have hh := primeListHalf n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
  simpa only [Nat.prod_primeFactorsList hn, ArithmeticFunction.cardFactors_apply] using hh

theorem factorTotientBound (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    l.prod ≤ 2 ^ (ArithmeticFunction.cardFactors l.prod) * (l.map Nat.totient).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have htail := ih (fun b hb => hl b (by simp [hb]))
    have hlpos : 0 < l.prod := List.prod_pos (by intro b hb; exact hl b (by simp [hb]))
    simp only [List.prod_cons, List.map_cons]
    rw [ArithmeticFunction.cardFactors_mul ha.ne' hlpos.ne']
    calc
      a * l.prod ≤ (2 ^ ArithmeticFunction.cardFactors a * a.totient) *
          (2 ^ ArithmeticFunction.cardFactors l.prod * (l.map Nat.totient).prod) :=
        Nat.mul_le_mul (totientHalf a) htail
      _ = _ := by rw [pow_add]; ring

#print axioms primeHalf
#print axioms primeListHalf
#print axioms totientHalf
#print axioms factorTotientBound
end AmicableTotient
