import WeightArithmetic
import DivisorSelection

namespace AmicableCoprimeDivisor
open scoped BigOperators
open AmicableManuscript

/-- Descending-prime selection used in Pollack's preliminary lemma. -/
theorem oddPrimeSelection (I : Finset ℕ)
    (hI : ∀ p ∈ I, p.Prime ∧ p ≠ 2) :
    ∃ D : Finset ℕ, D ⊆ I ∧
      (∀ p ∈ D, ∀ q ∈ D, ¬ p ∣ q + 1) ∧
      (∀ p ∈ I, p ∉ D → p ∣ ∏ q ∈ D, (q + 1)) := by
  classical
  induction I using Finset.strongInductionOn with
  | _ I ih =>
    by_cases hne : I.Nonempty
    · let p := I.max' hne
      have hpI : p ∈ I := Finset.max'_mem I hne
      have hp := (hI p hpI).1
      have hpodd := hp.eq_two_or_odd.resolve_left (hI p hpI).2
      let J := I.filter (fun q => q ≠ p ∧ ¬q ∣ p + 1)
      have hJI : J ⊆ I := Finset.filter_subset _ _
      have hpJ : p ∉ J := by simp [J]
      have hJlt : J ⊂ I := (Finset.ssubset_iff_subset_ne).mpr ⟨hJI, by
        intro heq
        exact hpJ (heq.symm ▸ hpI)⟩
      obtain ⟨D, hDJ, hDgood, hDrest⟩ := ih J hJlt (fun q hq => hI q (hJI hq))
      have hpD : p ∉ D := fun h => hpJ (hDJ h)
      have hpnot : ∀ q ∈ D, ¬p ∣ q + 1 := by
        intro q hq hdiv
        have hqJ := hDJ hq
        have hqI := hJI hqJ
        have hqne := (Finset.mem_filter.mp hqJ).2.1
        have hqle : q ≤ p := Finset.le_max' I q hqI
        have hqodd := (hI q hqI).1.eq_two_or_odd.resolve_left (hI q hqI).2
        have hple : p ≤ q + 1 := Nat.le_of_dvd (by omega) hdiv
        omega
      refine ⟨insert p D, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hpI (hDJ.trans hJI)
      · intro q hq r hr
        rcases Finset.mem_insert.mp hq with rfl | hq
        · rcases Finset.mem_insert.mp hr with rfl | hr
          · intro h
            have : p ∣ 1 := (Nat.dvd_add_iff_left (dvd_refl p)).mpr (by simpa [Nat.add_comm] using h)
            exact hp.not_dvd_one this
          · exact hpnot r hr
        · rcases Finset.mem_insert.mp hr with rfl | hr
          · exact (Finset.mem_filter.mp (hDJ hq)).2.2
          · exact hDgood q hq r hr
      · intro q hq hqD
        have hqp : q ≠ p := by intro h; subst q; exact hqD (Finset.mem_insert_self _ _)
        rw [Finset.prod_insert hpD]
        by_cases hqdiv : q ∣ p + 1
        · exact dvd_mul_of_dvd_left hqdiv _
        · exact dvd_mul_of_dvd_right (hDrest q (Finset.mem_filter.mpr ⟨hq, hqp, hqdiv⟩)
            (fun h => hqD (Finset.mem_insert_of_mem h))) _
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst I
      exact ⟨∅, by simp, by simp, by simp⟩

theorem oddSquarefreeDivisor {n : ℕ} (hn : Squarefree n) (hodd : ¬2 ∣ n) :
    ∃ d : ℕ, d ∣ n ∧ d.Coprime (sigma d) ∧ n / d ∣ sigma d := by
  classical
  obtain ⟨D, hDI, hDgood, hDrest⟩ := oddPrimeSelection n.primeFactors (by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    intro heq
    exact hodd (heq ▸ Nat.dvd_of_mem_primeFactors hp))
  let d := ∏ p ∈ D, p
  have hdvd : d ∣ n := (Finset.prod_dvd_prod_of_subset D n.primeFactors (fun p : ℕ => p) hDI).trans
    (Nat.prod_primeFactors_dvd n)
  have hdsf := hn.squarefree_of_dvd hdvd
  have hdp : d.primeFactors = D := Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hDI hp))
  have hsig : sigma d = ∏ p ∈ D, (p + 1) := by rw [AmicableWeight.sigma_squarefree hdsf, hdp]
  have hcop : d.Coprime (sigma d) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hps
    have hpD : p ∈ D := hdp ▸ Nat.mem_primeFactors.mpr ⟨hp, hpd, hdsf.ne_zero⟩
    rw [hsig] at hps
    obtain ⟨q, hqD, hpq⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hps
    exact hDgood p hpD q hqD hpq
  refine ⟨d, hdvd, hcop, ?_⟩
  rw [← Nat.prod_primeFactors_sdiff_of_squarefree hn hDI]
  have hsigpos : sigma d ≠ 0 := by rw [hsig]; exact Finset.prod_ne_zero_iff.mpr (by intros; omega)
  let E := n.primeFactors \ D
  have hEp : (∏ p ∈ E, p).primeFactors = E := Nat.primeFactors_prod (fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
  have hrad : ∏ p ∈ (∏ q ∈ E, q).primeFactors, p = ∏ p ∈ E, p := by rw [hEp]
  rw [← hrad, Nat.prod_primeFactors_dvd_iff hsigpos, hEp]
  intro p hp
  obtain ⟨hpI, hpD⟩ := Finset.mem_sdiff.mp hp
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpI,
    hsig ▸ hDrest p hpI hpD, hsigpos⟩

#print axioms oddPrimeSelection
#print axioms oddSquarefreeDivisor
end AmicableCoprimeDivisor


namespace AmicableCoprimeDivisor
open AmicableManuscript

theorem squarefreeDivisorFinite {n : ℕ} (hn : Squarefree n) :
    ∃ d : ℕ, d ∣ n ∧ d.Coprime (sigma d) ∧ n ≤ 2 * d * sigma d := by
  by_cases h2 : 2 ∣ n
  · have hn2 : n = 2 * (n / 2) := (Nat.mul_div_cancel' h2).symm
    have hsf : Squarefree (n / 2) := hn.squarefree_of_dvd (Nat.div_dvd_of_dvd h2)
    have hcop : Nat.Coprime 2 (n / 2) := Nat.coprime_of_squarefree_mul (hn2 ▸ hn)
    have hodd : ¬2 ∣ n / 2 := Nat.prime_two.coprime_iff_not_dvd.mp hcop
    obtain ⟨d, hd, hc, ht⟩ := oddSquarefreeDivisor hsf hodd
    have hdpos : 0 < d := Nat.pos_of_ne_zero (hsf.squarefree_of_dvd hd).ne_zero
    have hnpos : 0 < n / 2 := Nat.pos_of_ne_zero hsf.ne_zero
    have hquotpos : 0 < (n / 2) / d := Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos
    have hquot := Nat.le_of_dvd (by rw [sigma_eq_s_add_self]; omega) ht
    have heq : d * ((n / 2) / d) = n / 2 := Nat.mul_div_cancel' hd
    refine ⟨d, hd.trans (Nat.div_dvd_of_dvd h2), hc, ?_⟩
    nlinarith
  · obtain ⟨d, hd, hc, ht⟩ := oddSquarefreeDivisor hn h2
    have hdpos : 0 < d := Nat.pos_of_ne_zero (hn.squarefree_of_dvd hd).ne_zero
    have hquot := Nat.le_of_dvd (by rw [sigma_eq_s_add_self]; omega) ht
    have heq : d * (n / d) = n := Nat.mul_div_cancel' hd
    refine ⟨d, hd, hc, ?_⟩
    nlinarith

#print axioms squarefreeDivisorFinite
end AmicableCoprimeDivisor
