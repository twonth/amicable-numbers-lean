import ManuscriptArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace AmicableDivisors
open Filter
open scoped Topology

theorem exponentFactorBound {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℕ, (a : ℝ) + 1 ≤ C * ((2 : ℝ) ^ e) ^ a := by
  let c := e * Real.log 2
  have hc : 0 < c := mul_pos he (Real.log_pos (by norm_num))
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-c * t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
  have h0 : Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  have hlim : Tendsto (fun a : ℕ => ((a : ℝ) + 1) * Real.exp (-c * a))
      atTop (𝓝 0) := by
    simpa [add_mul, Function.comp_def] using (h1.add h0).comp tendsto_natCast_atTop_atTop
  obtain ⟨C, hC⟩ := hlim.bddAbove_range
  refine ⟨max C 1, le_max_right _ _, fun a => ?_⟩
  have ha : ((a : ℝ) + 1) * Real.exp (-c * a) ≤ max C 1 :=
    (hC (Set.mem_range_self a)).trans (le_max_left _ _)
  have hh := mul_le_mul_of_nonneg_right ha (Real.exp_pos (c * a)).le
  have hexp : Real.exp (-c * a) * Real.exp (c * a) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [mul_assoc, hexp, mul_one] at hh
  convert hh using 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
  congr 2
  dsimp [c]
  ring

theorem largePrimeFactorBound {e : ℝ} {p a : ℕ} (hp : 2 ≤ (p : ℝ) ^ e) :
    (a : ℝ) + 1 ≤ ((p : ℝ) ^ e) ^ a := by
  have ha : a + 1 ≤ 2 ^ a := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ]
      omega
  exact (by exact_mod_cast ha : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a).trans
    (pow_le_pow_left₀ (by norm_num) hp _)

theorem divisorPowerBound {e : ℝ} (he : 0 < e) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ e := by
  classical
  obtain ⟨C, hC1, hC⟩ := exponentFactorBound he
  have hpow : Tendsto (fun p : ℕ => (p : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow.eventually (eventually_ge_atTop 2))
  refine ⟨C ^ N, pow_pos (by linarith) _, fun n hn => ?_⟩
  let F := n.primeFactors
  have hpbound : ∀ p ∈ F, (n.factorization p : ℝ) + 1 ≤
      (if p < N then C else 1) * ((p : ℝ) ^ e) ^ n.factorization p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hsmall
    · exact (hC _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_le_rpow (by norm_num) hp2 he.le) _) (by linarith))
    · rw [one_mul]
      exact largePrimeFactorBound (hN p (by omega))
  have hprod := Finset.prod_le_prod₀ (fun p (_ : p ∈ F) => by positivity) hpbound
  have hcard : ((F.filter (fun p => p < N)).card) ≤ N := by
    calc
      _ ≤ (Finset.range N).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = N := Finset.card_range N
  have hfac : ∏ p ∈ F, ((p : ℝ) ^ e) ^ n.factorization p = (n : ℝ) ^ e := by
    have heq : ∀ p : ℕ, ((p : ℝ) ^ e) ^ n.factorization p =
        ((p : ℝ) ^ n.factorization p) ^ e := by
      intro p
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
        mul_comm e, Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    simp_rw [heq]
    rw [Real.finsetProd_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _)]
    have hbase : ∏ p ∈ F, (p : ℝ) ^ n.factorization p = (n : ℝ) := by
      have hh := Nat.prod_factorization_pow_eq_self hn.ne'
      simp only [Finsupp.prod, Nat.support_factorization] at hh
      exact_mod_cast hh
    rw [hbase]
  have hconst : ∏ p ∈ F, (if p < N then C else 1) ≤ C ^ N := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hC1 hcard
  have hleft : (n.divisors.card : ℝ) = ∏ p ∈ F, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn.ne']
    push_cast
    rfl
  rw [hleft]
  refine hprod.trans ?_
  rw [Finset.prod_mul_distrib, hfac]
  exact mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sigmaDivisorCountUniform {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ, (m : ℝ) ≤ x * Real.log x →
      ((AmicableManuscript.sigma m).divisors.card : ℝ) ≤ x ^ e := by
  obtain ⟨K, hK, hbound⟩ := divisorPowerBound (by linarith : 0 < e / 8)
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < e / 2)).eventually
    (eventually_ge_atTop K), eventually_gt_atTop (1 : ℝ)] with x hxK hx
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp [AmicableManuscript.sigma, Real.rpow_nonneg (by linarith : 0 ≤ x) e]
  have hspos : 0 < AmicableManuscript.sigma m := by
    rw [AmicableManuscript.sigma_eq_s_add_self]
    omega
  have hmX : (m : ℝ) ≤ x ^ 2 := by
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
    have hh := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ x)
    nlinarith
  have hsX : (AmicableManuscript.sigma m : ℝ) ≤ x ^ 4 := by
    have hs : (AmicableManuscript.sigma m : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 m
    have hh := sq_le_sq₀ (Nat.cast_nonneg m) (sq_nonneg x) |>.mpr hmX
    nlinarith
  calc
    _ ≤ K * (AmicableManuscript.sigma m : ℝ) ^ (e / 8) := hbound _ hspos
    _ ≤ K * (x ^ 4) ^ (e / 8) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hsX (by linarith)) hK.le
    _ = K * x ^ (e / 2) := by
      rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ x)]
      congr 2
      ring
    _ ≤ x ^ (e / 2) * x ^ (e / 2) := mul_le_mul_of_nonneg_right hxK
      (Real.rpow_nonneg (by linarith) _)
    _ = x ^ e := by
      rw [← Real.rpow_add (by linarith : 0 < x)]
      congr 1
      ring

#print axioms sigmaDivisorCountUniform
#print axioms divisorPowerBound
#print axioms exponentFactorBound
#print axioms largePrimeFactorBound
end AmicableDivisors



