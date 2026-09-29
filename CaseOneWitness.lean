import CaseOneRange
import CaseOneSelection
import ComplementaryDivisor
import DivisorAllocation

namespace AmicableCases
open AmicableManuscript AmicableWeight AmicableAllocation Filter
open scoped BigOperators Topology

/-- Case I's construction from the amicable pair and its squarefree unitary factor. -/
theorem caseOneWitness {e : ℝ} (he : 0 < e) (he1 : e < 1 / 10) :
    ∀ᶠ x : ℝ in atTop, ∀ (n n' a B p : ℕ), Amicable n n' →
      (n : ℝ) ≤ x * Real.log x → (n' : ℝ) ≤ x * Real.log x →
      n' = B * a → Squarefree a → B.Coprime a → a.Coprime n →
      x ^ (199 / 200 : ℝ) ≤ (a : ℝ) →
      p.Prime → p ∣ n → p.Coprime n' → p + 1 ∣ sigma n →
      x ^ (e ^ 2) ≤ (p : ℝ) → (p : ℝ) ≤ x ^ (4 / 5 : ℝ) →
      (∀ q ∈ a.primeFactors, q < p) →
      ∃ m R d : ℕ, CaseOneData x e n' m R d p := by
  classical
  filter_upwards [AmicableAbsorption.constantLogAbsorb 2 (by norm_num : (0 : ℝ) < 1 / 200),
    eventually_gt_atTop (1 : ℝ)] with x htwo hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos hx
  intro n n' a B p hpair hnX hn'X hn' hsf hBA han halower hp hpn hpn' hpsigma hplower hpupper hprimes
  have hnpos := hpair.1
  have hn'pos := hpair.2.1
  have hapos : 0 < a := Nat.pos_of_ne_zero hsf.ne_zero
  have hBpos : 0 < B := by
    by_contra hh
    have hB0 : B = 0 := by omega
    simp [hn', hB0] at hn'pos
  have hsB : 0 < sigma B := by rw [sigma_eq_s_add_self]; omega
  have hdiv : p + 1 ∣ sigma B * sigma a := by
    have hs := amicable_sigma hpair
    rw [hs.1, ← hs.2, hn', sigma_mul hBA] at hpsigma
    exact hpsigma
  let g := Nat.gcd (p + 1) (sigma B)
  let r := (p + 1) / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgdiv : g ∣ p + 1 := Nat.gcd_dvd_left _ _
  have hgr : g * r = p + 1 := Nat.mul_div_cancel' hgdiv
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd (by omega) hgdiv) hg
  have hrdiv : r ∣ sigma a := quotientGcdDivides (by omega) hdiv
  have hrg : r ≤ p + 1 := Nat.div_le_self _ _
  have hrupper : (r : ℝ) ≤ x ^ (161 / 200 : ℝ) := by
    have hh2 : 2 ≤ x ^ (1 / 200 : ℝ) := by nlinarith
    have hp1 : 1 ≤ x ^ (4 / 5 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    calc
      (r : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hrg
      _ ≤ 2 * x ^ (4 / 5 : ℝ) := by linarith
      _ ≤ x ^ (1 / 200 : ℝ) * x ^ (4 / 5 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  rw [sigma_squarefree hsf] at hrdiv
  obtain ⟨f, hfdiv, hfprod⟩ := distributeDivisor a.primeFactors (fun q => q + 1) hrdiv
  have hfpos : ∀ q ∈ a.primeFactors, 0 < f q := by
    intro q hq
    exact Nat.pos_of_dvd_of_pos (hfdiv q hq) (by omega)
  let J := a.primeFactors.filter (fun q => (f q : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ))
  let r0 := ∏ q ∈ J, q
  have hJ : J ⊆ a.primeFactors := Finset.filter_subset _ _
  have hr0div : r0 ∣ a := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_dvd_prod_of_subset J a.primeFactors (fun q => q) hJ
  have hr0sf := hsf.squarefree_of_dvd hr0div
  have hr0pf : r0.primeFactors = J := Nat.primeFactors_prod (fun q hq => Nat.prime_of_mem_primeFactors (hJ hq))
  have hgood := goodPrimeProduct a.primeFactors f (fun q hq => Nat.prime_of_mem_primeFactors hq) hfpos
  have hprodA : (∏ q ∈ a.primeFactors, (q : ℝ)) = (a : ℝ) := by
    simpa only [Nat.cast_prod] using congrArg (fun z : ℕ => (z : ℝ)) (Nat.prod_primeFactors_of_squarefree hsf)
  have hprodf : (∏ q ∈ a.primeFactors, (f q : ℝ)) = (r : ℝ) := by exact_mod_cast hfprod
  rw [hprodA, hprodf] at hgood
  have hgood' : (a : ℝ) / (r : ℝ) ^ (10 / 9 : ℝ) ≤ (r0 : ℝ) := by simpa only [r0, J, Nat.cast_prod] using hgood
  have hr0lower := goodProductPowerLower hx (by exact_mod_cast hrpos) hgood' halower hrupper
  have hU : 1 ≤ x ^ (e ^ 2 / 10) := Real.one_le_rpow hx.le (by positivity)
  have hU0 : x ^ (e ^ 2 / 10) < (r0 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx.le (by nlinarith [sq_nonneg (e - 1 / 10)] : e ^ 2 / 10 ≤ 1 / 10)).trans_lt hr0lower
  obtain ⟨R, hRr0, hRlower, hRtypes⟩ := caseOneSelectR hr0sf hU hU0 (by
    intro q hq
    rw [hr0pf] at hq
    exact hprimes q (hJ hq))
  have hRa : R ∣ a := hRr0.trans hr0div
  have hRsf := hsf.squarefree_of_dvd hRa
  have hRpos : 0 < R := Nat.pos_of_ne_zero hRsf.ne_zero
  obtain ⟨d, hddiv, hdprod, hdsize⟩ := complementaryDivisor hsf hRa hBA
    (Nat.gcd_dvd_right _ _) hgr.symm f hfdiv hfprod (by
      intro q hq
      have hqr0 : q ∈ r0.primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq, (Nat.dvd_of_mem_primeFactors hq).trans hRr0, hr0sf.ne_zero⟩
      rw [hr0pf] at hqr0
      exact (Finset.mem_filter.mp hqr0).2)
  let m := B * (a / R)
  have hmR : n' = m * R := by dsimp [m]; rw [mul_assoc, Nat.div_mul_cancel hRa, hn']
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    simp [hmR, hm0] at hn'pos
  have hcop : m.Coprime R := (hBA.of_dvd_right hRa).mul_left
    (Nat.coprime_of_squarefree_mul (show Squarefree (a / R * R) by rw [Nat.div_mul_cancel hRa]; exact hsf))
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (hdprod ▸ dvd_mul_right d (∏ q ∈ R.primeFactors, f q)) (by omega)
  refine ⟨m, R, d, hmpos, hRpos, hmR, hn'X, hp, ?_, hplower, hRlower,
    hcop, ?_, hpn', ?_, ?_, hdpos, hddiv, ?_, hdsize⟩
  · exact (by exact_mod_cast Nat.le_of_dvd hnpos hpn : (p : ℝ) ≤ n).trans hnX
  · rw [hpair.2.2.2.2]
    exact han.of_dvd_left hRa
  · rw [hpair.2.2.2.2]
    exact hpn
  · rcases hRtypes with hh | hh
    · exact Or.inl hh
    · right
      rw [← Real.rpow_mul_natCast hx0.le] at hh
      convert hh using 1 <;> ring
  · exact hdprod ▸ dvd_mul_right d (∏ q ∈ R.primeFactors, f q)

#print axioms caseOneWitness
end AmicableCases
