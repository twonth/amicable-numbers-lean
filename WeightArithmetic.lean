import ManuscriptArithmetic
import RankinFinite

namespace AmicableWeight
open scoped BigOperators
open AmicableManuscript

noncomputable def primeWeight (y : ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ y then (p : ℝ) else y

noncomputable def H (y : ℝ) (n : ℕ) : ℝ :=
  n.factorization.prod fun p e => (primeWeight y p) ^ e

noncomputable def smallPart (y : ℝ) (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => if (p : ℝ) ≤ y then p ^ e else 1

noncomputable def roughOmega (y : ℝ) (n : ℕ) : ℕ :=
  n.factorization.sum fun p e => if (p : ℝ) ≤ y then 0 else e

theorem H_eq_smallPart_mul (y : ℝ) (n : ℕ) :
    H y n = (smallPart y n : ℝ) * y ^ roughOmega y n := by
  unfold H smallPart roughOmega Finsupp.prod Finsupp.sum
  rw [Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  unfold primeWeight
  dsimp only
  split_ifs <;> simp

theorem H_one (y : ℝ) : H y 1 = 1 := by simp [H]

theorem H_mul (y : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    H y (m * n) = H y m * H y n := by
  unfold H
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem H_pos {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 < H y n := by
  unfold H Finsupp.prod
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  apply pow_pos
  unfold primeWeight
  split_ifs <;> assumption

theorem smallPart_pos (y : ℝ) (n : ℕ) : 0 < smallPart y n := by
  unfold smallPart Finsupp.prod
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  dsimp only
  split_ifs
  · exact pow_pos hprime.pos _
  · exact Nat.one_pos

theorem log_H {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.log (H y n) = Real.log (smallPart y n) +
      Real.log y * (roughOmega y n : ℝ) := by
  rw [H_eq_smallPart_mul, Real.log_mul (by exact_mod_cast (smallPart_pos y n).ne')
    (pow_ne_zero _ hy.ne'), Real.log_pow]
  ring

theorem H_prime (y : ℝ) {p : ℕ} (hp : p.Prime) :
    H y p = primeWeight y p := by
  simp [H, hp.factorization]

theorem H_prod {ι : Type*} (I : Finset ι) (f : ι → ℕ) (y : ℝ)
    (hf : ∀ i ∈ I, f i ≠ 0) :
    H y (∏ i ∈ I, f i) = ∏ i ∈ I, H y (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [H_one]
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, H_mul y]
    · rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    · exact hf i (Finset.mem_insert_self _ _)
    · exact Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem sigma_squarefree {b : ℕ} (hb : Squarefree b) :
    sigma b = ∏ q ∈ b.primeFactors, (q + 1) := by
  calc
    sigma b = ∏ q ∈ b.primeFactors, sigma q :=
      (ArithmeticFunction.isMultiplicative_sigma.prod_primeFactors hb).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q hq
      exact sigma_prime (Nat.prime_of_mem_primeFactors hq)

theorem H_sigma_squarefree (y : ℝ) {b : ℕ} (hb : Squarefree b) :
    H y (sigma b) = ∏ q ∈ b.primeFactors, H y (q + 1) := by
  rw [sigma_squarefree hb, H_prod]
  intro q _
  omega

theorem weightedSigmaProduct {y : ℝ} (hy : 0 < y) (eta t : ℝ)
    {b : ℕ} (hb : Squarefree b) :
    H y (sigma b) ^ eta / (b : ℝ) ^ t =
      ∏ q ∈ b.primeFactors, H y (q + 1) ^ eta / (q : ℝ) ^ t := by
  rw [Finset.prod_div_distrib,
    Real.finsetProd_rpow _ _ (fun q _ => (H_pos hy (q + 1)).le),
    Real.finsetProd_rpow _ _ (fun q _ => Nat.cast_nonneg q),
    ← H_sigma_squarefree y hb, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hb]

theorem weightedSigmaEulerBound {y : ℝ} (hy : 0 < y)
    (B P : Finset ℕ) (eta t : ℝ)
    (hB : ∀ b ∈ B, Squarefree b) (hP : ∀ b ∈ B, b.primeFactors ⊆ P) :
    ∑ b ∈ B, H y (sigma b) ^ eta / (b : ℝ) ^ t ≤
      Real.exp (∑ q ∈ P, H y (q + 1) ^ eta / (q : ℝ) ^ t) := by
  let w : ℕ → ℝ := fun q => H y (q + 1) ^ eta / (q : ℝ) ^ t
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    exact div_nonneg (Real.rpow_nonneg (H_pos hy _).le _)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  calc
    _ = ∑ b ∈ B, ∏ q ∈ b.primeFactors, w q := by
      apply Finset.sum_congr rfl
      intro b hb
      exact weightedSigmaProduct hy eta t (hB b hb)
    _ ≤ ∏ q ∈ P, (1 + w q) :=
      AmicableRankin.finiteSquarefreeEulerBound B P w hw hB hP
    _ ≤ _ := AmicableRankin.finiteEulerExpBound P w hw

theorem weightedSigmaRankinFinite {y : ℝ} (hy : 0 < y)
    (B P : Finset ℕ) (Y K eta delta : ℝ)
    (hY : 0 < Y) (hK : 0 < K) (heta : 0 < eta) (hdelta : 0 < delta)
    (hB : ∀ b ∈ B, Squarefree b ∧ (b : ℝ) ≤ Y ∧ K < H y (sigma b))
    (hP : ∀ b ∈ B, b.primeFactors ⊆ P) :
    (B.card : ℝ) ≤ Y ^ (1 + delta) * K ^ (-eta) *
      Real.exp (∑ q ∈ P, H y (q + 1) ^ eta / (q : ℝ) ^ (1 + delta)) := by
  have hr := AmicableRankin.finiteRankin B (fun b => H y (sigma b))
    Y K eta delta hY hK heta hdelta (fun b hb =>
      ⟨Nat.pos_of_ne_zero (hB b hb).1.ne_zero, (hB b hb).2⟩)
  exact hr.trans (mul_le_mul_of_nonneg_left
    (weightedSigmaEulerBound hy B P eta (1 + delta) (fun b hb => (hB b hb).1) hP)
    (by positivity))

#print axioms H_one
#print axioms H_eq_smallPart_mul
#print axioms H_mul
#print axioms H_pos
#print axioms smallPart_pos
#print axioms log_H
#print axioms H_prime
#print axioms H_prod
#print axioms sigma_squarefree
#print axioms H_sigma_squarefree
#print axioms weightedSigmaProduct
#print axioms weightedSigmaEulerBound
#print axioms weightedSigmaRankinFinite
end AmicableWeight
