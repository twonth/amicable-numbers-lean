import ManuscriptArithmetic
import Mathlib.Data.Nat.Totient

namespace AmicableHarmonic
open scoped BigOperators

theorem removeMultiples (F : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hpos : ∀ n ∈ F, 0 < n)
    (hclosed : ∀ n ∈ F, p ∣ n → n / p ∈ F) :
    (1 - (1 : ℝ) / p) * ∑ n ∈ F, (1 : ℝ) / n ≤
      ∑ n ∈ F.filter (fun n => ¬p ∣ n), (1 : ℝ) / n := by
  classical
  let D := F.filter (fun n => p ∣ n)
  have hinj : Set.InjOn (fun n : ℕ => n / p) D := by
    intro n hn m hm hnm
    have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hm' := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    change n / p = m / p at hnm
    rw [hnm] at hn'
    omega
  have hsub : D.image (fun n => n / p) ⊆ F := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact hclosed n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have hdiv : ∑ n ∈ D, (1 : ℝ) / n ≤ (1 / p) * ∑ n ∈ F, (1 : ℝ) / n := by
    calc
      _ = (1 / p : ℝ) * ∑ n ∈ D, (1 : ℝ) / (n / p : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
        have hncast : ((n / p : ℕ) : ℝ) * p = n := by exact_mod_cast hn'
        rw [← hncast, one_div_mul_one_div]
        congr 1
        ring
      _ = (1 / p : ℝ) * ∑ a ∈ D.image (fun n => n / p), (1 : ℝ) / a := by
        rw [Finset.sum_image hinj]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)) (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun n => p ∣ n) (fun n => (1 : ℝ) / n)
  change (∑ n ∈ D, (1 : ℝ) / n) + _ = _ at hsplit
  nlinarith

theorem sieveHarmonicLower (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬p ∣ n), (1 : ℝ) / n := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hprime := hP p (Finset.mem_insert_self _ _)
    have hP' := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    let F := (Finset.Icc 1 N).filter (fun n => ∀ q ∈ P, ¬q ∣ n)
    have hpos : ∀ n ∈ F, 0 < n := fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hclosed : ∀ n ∈ F, p ∣ n → n / p ∈ F := by
      intro n hn hpn
      obtain ⟨hnI, hnP⟩ := Finset.mem_filter.mp hn
      have hn0 := (Finset.mem_Icc.mp hnI).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd hn0 hpn) hprime.pos
      · exact (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hnI).2
      · intro q hq hqd
        exact hnP q hq (hqd.trans (Nat.div_dvd_of_dvd hpn))
    have hr := removeMultiples F hprime.pos hpos hclosed
    have hnonneg : 0 ≤ 1 - (1 : ℝ) / p := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1
      norm_num at hh
      simpa only [one_div] using sub_nonneg.mpr hh
    rw [Finset.prod_insert hp, mul_assoc]
    refine (mul_le_mul_of_nonneg_left (ih hP') hnonneg).trans ?_
    convert hr using 1
    congr 1
    ext n
    simp [F, and_assoc, and_left_comm, and_comm]

theorem totientRatioProduct {d : ℕ} (hd : 0 < d) :
    (d.totient : ℝ) / d = ∏ p ∈ d.primeFactors, (1 - (1 : ℝ) / p) := by
  have hh := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at hh
  rw [hh]
  field_simp

theorem coprimePrimeFactors {d n : ℕ} (hd : d ≠ 0) :
    (∀ p ∈ d.primeFactors, ¬p ∣ n) ↔ n.Coprime d := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpn, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩) hpn
  · intro h p hp hpn
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, Nat.prime_of_mem_primeFactors hp, hpn, Nat.dvd_of_mem_primeFactors hp⟩) h

theorem coprimeHarmonicLower (N d : ℕ) (hd : 0 < d) :
    ((d.totient : ℝ) / d) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime d), (1 : ℝ) / n := by
  rw [totientRatioProduct hd]
  simpa only [coprimePrimeFactors hd.ne'] using
    sieveHarmonicLower d.primeFactors N (fun p hp => Nat.prime_of_mem_primeFactors hp)

#print axioms totientRatioProduct
#print axioms coprimePrimeFactors
#print axioms coprimeHarmonicLower
#print axioms removeMultiples
#print axioms sieveHarmonicLower
end AmicableHarmonic

