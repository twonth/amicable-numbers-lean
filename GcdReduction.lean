import LargeCoprimeDivisor
import DivisorSelection

namespace AmicableGcdReduction
open AmicableManuscript Filter
open scoped Topology

theorem sigmaComplement {n d : ℕ} (hn : Squarefree n) (hd : d ∣ n)
    (hc : d.Coprime (sigma d)) (hs : d ∣ sigma n) : d ∣ sigma (n / d) := by
  have heq : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  have hcop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (heq ▸ hn)
  rw [heq, sigma_mul hcop] at hs
  exact hc.dvd_of_dvd_mul_left hs

theorem primeSigmaComplement {n p : ℕ} (hn : Squarefree n) (hp : p.Prime)
    (hd : p ∣ n) (hs : p ∣ sigma n) : p ∣ sigma (n / p) := by
  apply sigmaComplement hn hd _ hs
  rw [sigma_prime hp, Nat.coprime_self_add_right]
  exact Nat.coprime_one_right p

/-- The two alternatives at the start of Pollack's squarefree gcd estimate. -/
theorem squarefreeGcdAlternatives : ∀ᶠ A : ℝ in atTop, ∀ n : ℕ,
    Squarefree n → A < (Nat.gcd n (sigma n) : ℝ) →
    (∃ p : ℕ, p.Prime ∧ A ^ (1 / 2 : ℝ) < p ∧ p ∣ n ∧ p ∣ sigma (n / p)) ∨
    (∃ d : ℕ, A ^ (1 / 6 : ℝ) < d ∧ (d : ℝ) ≤ A ∧ d ∣ n ∧
      d.Coprime (sigma d) ∧ d ∣ sigma (n / d)) := by
  obtain ⟨N, hN⟩ := AmicableCoprimeDivisor.largeCoprimeDivisor (e := (1 / 6 : ℝ)) (by norm_num)
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
    (eventually_ge_atTop (N : ℝ)), eventually_gt_atTop (1 : ℝ)] with A hAN hA
  intro n hn hg
  let G := Nat.gcd n (sigma n)
  have hGsf : Squarefree G := hn.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
  by_cases hlarge : ∃ p ∈ G.primeFactors, A ^ (1 / 2 : ℝ) < (p : ℝ)
  · obtain ⟨p, hpG, hpA⟩ := hlarge
    have hp := Nat.prime_of_mem_primeFactors hpG
    have hpn := (Nat.dvd_of_mem_primeFactors hpG).trans (Nat.gcd_dvd_left _ _)
    have hps := (Nat.dvd_of_mem_primeFactors hpG).trans (Nat.gcd_dvd_right _ _)
    exact Or.inl ⟨p, hp, hpA, hpn, primeSigmaComplement hn hp hpn hps⟩
  · have hAsqrt : 1 ≤ A ^ (1 / 2 : ℝ) := Real.one_le_rpow hA.le (by norm_num)
    have hrootA : A ^ (1 / 2 : ℝ) ≤ A := by
      conv_rhs => rw [← Real.rpow_one A]
      exact Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)
    obtain ⟨D, hDG, hAD, hDA⟩ := AmicableSelection.squarefreeDivisorCrossing hGsf hAsqrt
      (hrootA.trans_lt hg) (by
        intro p hp
        by_contra h
        exact hlarge ⟨p, hp, lt_of_not_ge h⟩)
    have hDA' : (D : ℝ) ≤ A := by
      simpa only [← Real.rpow_add (by linarith : 0 < A), show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
        Real.rpow_one] using hDA
    have hDN : N ≤ D := by exact_mod_cast (hAN.trans hAD.le)
    have hDsf : Squarefree D := hGsf.squarefree_of_dvd hDG
    obtain ⟨d, hdD, hc, hdlower⟩ := hN D hDN hDsf
    have hdn := hdD.trans (hDG.trans (Nat.gcd_dvd_left _ _))
    have hds := hdD.trans (hDG.trans (Nat.gcd_dvd_right _ _))
    refine Or.inr ⟨d, ?_, ?_, hdn, hc, sigmaComplement hn hdn hc hds⟩
    · have hh := Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith : 0 ≤ A) _) hAD (by norm_num : (0 : ℝ) < 1 / 3)
      rw [← Real.rpow_mul (by linarith : 0 ≤ A)] at hh
      norm_num at hh hdlower
      exact hh.trans_le hdlower
    · exact (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hDsf.ne_zero) hdD)).trans hDA'

#print axioms sigmaComplement
#print axioms primeSigmaComplement
#print axioms squarefreeGcdAlternatives
end AmicableGcdReduction
