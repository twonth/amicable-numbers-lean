import CaseTwoWitness
import TechnicalLemma

namespace AmicableCases
open AmicableManuscript AmicableWeight AmicableSelection Filter
open scoped Topology

theorem caseTwoPairWitness {e delta : ℝ} (he : 0 < e) (he1 : e < 1 / 10)
    (hd0 : 0 < delta) (hd : delta ≤ selectionGap e / 4) :
    ∀ᶠ x : ℝ in atTop, ∀ (n n' a a' B B' : ℕ), Amicable n n' →
      n = B * a → n' = B' * a' → Squarefree a → Squarefree a' →
      B.Coprime a → B'.Coprime a' → a.Coprime n' → a'.Coprime n →
      (n : ℝ) ≤ x * Real.log x → (n' : ℝ) ≤ x * Real.log x →
      (∀ p ∈ a.primeFactors, (p : ℝ) ≤ x ^ (e ^ 2)) →
      (∀ p ∈ a'.primeFactors, (p : ℝ) ≤ x ^ (e ^ 2)) →
      (1 - delta / 4) * Real.log x ≤ Real.log (a : ℝ) →
      (1 - delta / 4) * Real.log x ≤ Real.log (a' : ℝ) →
      Real.log (a' : ℝ) ≤ (1 + delta / 4) * Real.log x →
      Real.log (sigma B' : ℝ) ≤ delta / 4 * Real.log x →
      (∃ b : ℕ, b ∣ n ∧ b ∈ AmicableTechnical.exceptionalSet (1 / 2 - 4 * e) x (x * Real.log x)) ∨
      ∃ m R d V : ℕ, CaseTwoData x e n m R d V := by
  classical
  filter_upwards [caseTwoWitness he he1 hd0 hd, eventually_gt_atTop (Real.exp 2)] with x hwitness hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  intro n n' a a' B B' hpair hn hn' hsf hsf' hBA hBA' han' ha'n hnX hn'X
    hprimes hprimes' halog ha'log ha'upper hB'log
  have hapos : 0 < a := Nat.pos_of_ne_zero hsf.ne_zero
  have ha'pos : 0 < a' := Nat.pos_of_ne_zero hsf'.ne_zero
  have hBpos : 0 < B := by
    by_contra hh
    have : B = 0 := by omega
    have hnpos := hpair.1
    simp [hn, this] at hnpos
  have hB'pos : 0 < B' := by
    by_contra hh
    have : B' = 0 := by omega
    have hnpos := hpair.2.1
    simp [hn', this] at hnpos
  have hU : 1 ≤ x ^ e := Real.one_le_rpow hx1.le he.le
  have hgapupper : selectionGap e < 1 := by dsimp [selectionGap]; nlinarith [sq_nonneg e, mul_nonneg he.le (sq_nonneg e)]
  have haU : x ^ e < (a : ℝ) := by
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 _) (by exact_mod_cast hapos)).mp
    rw [Real.log_rpow hx0]
    have hc : e < 1 - delta / 4 := by nlinarith
    nlinarith
  obtain ⟨R, hRa, hRlo, hRhi⟩ := squarefreeDivisorCrossing hsf hU haU hprimes
  have hRpos : 0 < R := Nat.pos_of_dvd_of_pos hRa hapos
  let b := a / R
  let m := B * b
  have hab : b * R = a := Nat.div_mul_cancel hRa
  have hbdiv : b ∣ a := Nat.div_dvd_of_dvd hRa
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hapos
  have hmpos : 0 < m := Nat.mul_pos hBpos hbpos
  have hbn : b ∣ n := hbdiv.trans (hn ▸ dvd_mul_left a B)
  have heqn : n = m * R := by dsimp [m]; rw [mul_assoc, hab, hn]
  have hcopbR : b.Coprime R := Nat.coprime_of_squarefree_mul (hab ▸ hsf)
  have hcopmR : m.Coprime R := (hBA.of_dvd_right hRa).mul_left hcopbR
  have hsbm : sigma b ∣ sigma m := by
    dsimp [m]
    rw [sigma_mul (hBA.of_dvd_right hbdiv)]
    exact dvd_mul_left _ _
  have hsbn : sigma b ∣ sigma n := by
    rw [heqn, sigma_mul hcopmR]
    exact hsbm.trans (dvd_mul_right _ _)
  have hsba : sigma b ∣ sigma B' * sigma a' := by
    have hs := amicable_sigma hpair
    rw [hs.1, ← hs.2, hn', sigma_mul hBA'] at hsbn
    exact hsbn
  have hbX : (b : ℝ) ≤ x * Real.log x :=
    (by exact_mod_cast Nat.le_of_dvd hpair.1 hbn : (b : ℝ) ≤ n).trans hnX
  by_cases hbad : b ∈ AmicableTechnical.exceptionalSet (1 / 2 - 4 * e) x (x * Real.log x)
  · exact Or.inl ⟨b, hbn, hbad⟩
  right
  have hmass : Real.log (smallPart (Real.log x) (sigma b) : ℝ) +
      Real.log (Real.log x) * (roughOmega (Real.log x) (sigma b) : ℝ) ≤
        (1 / 2 - 4 * e) * Real.log x := by
    by_contra hh
    apply hbad
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Nat.le_floor hbX; omega),
      hsf.squarefree_of_dvd hbdiv, lt_of_not_ge hh⟩
  have hRhi' : (R : ℝ) ≤ x ^ (e + e ^ 2) := by simpa only [← Real.rpow_add hx0] using hRhi
  have ha'X : (a' : ℝ) ≤ x * Real.log x :=
    (by exact_mod_cast Nat.le_mul_of_pos_left a' hB'pos : (a' : ℝ) ≤ B' * a').trans (by simpa only [hn', Nat.cast_mul] using hn'X)
  have hratio : Real.log ((a' : ℝ) / b) + Real.log (sigma B' : ℝ) ≤
      (e + e ^ 2 + delta) * Real.log x := by
    have hlogR := Real.log_le_log (by exact_mod_cast hRpos : (0 : ℝ) < R) hRhi'
    rw [Real.log_rpow hx0] at hlogR
    have hloga : Real.log (b : ℝ) + Real.log (R : ℝ) = Real.log (a : ℝ) := by
      rw [← Real.log_mul (by exact_mod_cast hbpos.ne') (by exact_mod_cast hRpos.ne')]
      exact congrArg Real.log (by exact_mod_cast hab)
    rw [Real.log_div (by exact_mod_cast ha'pos.ne') (by exact_mod_cast hbpos.ne')]
    nlinarith
  obtain ⟨d,V,hw⟩ := hwitness n m R b a' B' hmpos hRpos hbpos hB'pos heqn hnX hRlo.le hRhi' hcopmR
    (by rw [hpair.2.2.2.1]; exact han'.of_dvd_left hRa) ha'n hsf' ha'X
    (by rw [hpair.2.2.2.1, hn']; exact dvd_mul_left _ _) hprimes' hsbm hsba
    (by nlinarith) hratio hmass
  exact ⟨m,R,d,V,hw⟩

#print axioms caseTwoPairWitness
end AmicableCases
