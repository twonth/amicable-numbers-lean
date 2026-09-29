import DivisorAllocation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

namespace AmicablePartitions
open scoped BigOperators

noncomputable def factorsOfAssignment {J h : ℕ} (v : Fin J → ℕ) (f : Fin J → Fin h) (j : Fin h) : ℕ :=
  ∏ i, if f i = j then v i else 1

theorem primeProductAllocation (J h : ℕ) (v : Fin J → ℕ) (hv : ∀ i, (v i).Prime)
    (g : Fin h → ℕ) (hg : ∏ j, g j = ∏ i, v i) :
    ∃ f : Fin J → Fin h, ∀ j, factorsOfAssignment v f j = g j := by
  classical
  induction J generalizing g with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro j
    have hg1 : ∏ j, g j = 1 := by simpa using hg
    have hj := (Finset.prod_eq_one_iff.mp hg1) j (Finset.mem_univ j)
    simpa [factorsOfAssignment] using hj.symm
  | succ J ih =>
    have hp := hv 0
    have hpdiv : v 0 ∣ ∏ j, g j := by rw [hg, Fin.prod_univ_succ]; exact dvd_mul_right _ _
    obtain ⟨j, _, hj⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hpdiv
    let g' := Function.update g j (g j / v 0)
    have hg' : ∏ k, g' k = ∏ i : Fin J, v i.succ := by
      have hupdate : ∏ k, g' k = (g j / v 0) * ∏ k ∈ Finset.univ.erase j, g k := by
        simpa only [Finset.sdiff_singleton_eq_erase] using
          Finset.prod_update_of_mem (Finset.mem_univ j) g (g j / v 0)
      have hprod : ∏ k, g k = g j * ∏ k ∈ Finset.univ.erase j, g k :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
      have hdiv := Nat.mul_div_cancel' hj
      rw [hprod, Fin.prod_univ_succ] at hg
      rw [hupdate]
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [← mul_assoc, hdiv]
      exact hg
    obtain ⟨f, hf⟩ := ih (fun i => v i.succ) (fun i => hv i.succ) g' hg'
    refine ⟨Fin.cons j f, ?_⟩
    intro k
    simp only [factorsOfAssignment, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change (if j = k then v 0 else 1) * factorsOfAssignment (fun i : Fin J => v i.succ) f k = g k
    rw [hf]
    by_cases hkj : k = j
    · subst k
      simp only [ite_true, g', Function.update_self]
      exact Nat.mul_div_cancel' hj
    · simp [g', Function.update_of_ne hkj, Ne.symm hkj]

theorem orderedFactorizationsBound {J h : ℕ} (v : Fin J → ℕ) (hv : ∀ i, (v i).Prime)
    (B : Finset (Fin h → ℕ)) (hB : ∀ g ∈ B, ∏ j, g j = ∏ i, v i) :
    B.card ≤ h ^ J := by
  classical
  have hsub : B ⊆ Finset.univ.image (fun f : Fin J → Fin h => factorsOfAssignment v f) := by
    intro g hg
    obtain ⟨f, hf⟩ := primeProductAllocation J h v hv g (hB g hg)
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, funext hf⟩
  exact (Finset.card_le_card hsub).trans (by simpa using
    (Finset.card_image_le (s := Finset.univ) (f := fun f : Fin J → Fin h => factorsOfAssignment v f)))

#print axioms primeProductAllocation
#print axioms orderedFactorizationsBound
end AmicablePartitions


namespace AmicablePartitions
open scoped BigOperators

theorem factorListLength {J : ℕ} (v : Fin J → ℕ) (hv : ∀ i, (v i).Prime)
    (l : List ℕ) (hl : ∀ a ∈ l, 1 < a) (hprod : l.prod = ∏ i, v i) : l.length ≤ J := by
  have hg : ∏ j : Fin l.length, l.get j = ∏ i, v i := by
    rw [← List.prod_ofFn, List.ofFn_get]
    exact hprod
  obtain ⟨f, hf⟩ := primeProductAllocation J l.length v hv l.get hg
  have hsurj : Function.Surjective f := by
    intro j
    by_contra h
    have hnone : ∀ i, f i ≠ j := by simpa only [not_exists] using h
    have hval : factorsOfAssignment v f j = 1 := by simp [factorsOfAssignment, hnone]
    have hgt := hl (l.get j) (List.get_mem l j)
    rw [hf] at hval
    omega
  simpa using Fintype.card_le_of_surjective f hsurj

noncomputable def paddedFactors (J : ℕ) (l : List ℕ) (i : Fin J) : ℕ := l.getD i.val 1

theorem paddedProduct (J : ℕ) (l : List ℕ) (hl : l.length ≤ J) :
    ∏ i, paddedFactors J l i = l.prod := by
  induction J generalizing l with
  | zero =>
    have heq : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    simp [paddedFactors]
  | succ J ih =>
    cases l with
    | nil => simp [paddedFactors]
    | cons a l =>
      have hlen : l.length ≤ J := by simpa using hl
      rw [Fin.prod_univ_succ]
      simpa [paddedFactors] using congrArg (fun n : ℕ => a * n) (ih l hlen)

theorem paddedInjective (J : ℕ) (l k : List ℕ)
    (hl : l.length ≤ J) (hk : k.length ≤ J)
    (hl1 : ∀ a ∈ l, 1 < a) (hk1 : ∀ a ∈ k, 1 < a)
    (heq : paddedFactors J l = paddedFactors J k) : l = k := by
  induction J generalizing l k with
  | zero =>
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    have hk0 : k = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hl0, hk0]
  | succ J ih =>
    cases l with
    | nil =>
      cases k with
      | nil => rfl
      | cons b k =>
        have hh := congrFun heq 0
        simp [paddedFactors] at hh
        have hb := hk1 b (by simp)
        omega
    | cons a l =>
      cases k with
      | nil =>
        have hh := congrFun heq 0
        simp [paddedFactors] at hh
        have ha := hl1 a (by simp)
        omega
      | cons b k =>
        have hab : a = b := by simpa [paddedFactors] using congrFun heq 0
        have htail : paddedFactors J l = paddedFactors J k := by
          funext i
          simpa [paddedFactors] using congrFun heq i.succ
        have hlk := ih l k (by simpa using hl) (by simpa using hk)
          (fun a ha => hl1 a (by simp [ha])) (fun b hb => hk1 b (by simp [hb])) htail
        simp [hab, hlk]

/-- Includes all possible numbers of factors; no fixed-length hypothesis is needed. -/
theorem allFactorListsBound {J : ℕ} (v : Fin J → ℕ) (hv : ∀ i, (v i).Prime)
    (B : Finset (List ℕ)) (hB : ∀ l ∈ B, (∀ a ∈ l, 1 < a) ∧ l.prod = ∏ i, v i) :
    B.card ≤ J ^ J := by
  classical
  have hlen := fun l hl => factorListLength v hv l (hB l hl).1 (hB l hl).2
  have hinj : Set.InjOn (paddedFactors J) B := by
    intro l hl k hk h
    exact paddedInjective J l k (hlen l hl) (hlen k hk) (hB l hl).1 (hB k hk).1 h
  rw [← Finset.card_image_of_injOn hinj]
  apply orderedFactorizationsBound v hv
  intro g hg
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hg
  rw [paddedProduct J l (hlen l hl)]
  exact (hB l hl).2

#print axioms factorListLength
#print axioms paddedProduct
#print axioms paddedInjective
#print axioms allFactorListsBound
end AmicablePartitions

namespace AmicablePartitions
open scoped BigOperators

theorem factorListLengthNat {d : ℕ} (hd : 0 < d) (l : List ℕ)
    (hl : ∀ a ∈ l, 1 < a) (hprod : l.prod = d) : l.length ≤ ArithmeticFunction.cardFactors d := by
  let v := d.primeFactorsList.get
  have hv : ∀ i, (v i).Prime := fun i => Nat.prime_of_mem_primeFactorsList (List.get_mem _ i)
  have hp : l.prod = ∏ i, v i := by
    rw [← List.prod_ofFn, List.ofFn_get, Nat.prod_primeFactorsList hd.ne']
    exact hprod
  exact factorListLength v hv l hl hp

theorem allFactorListsBoundNat {d : ℕ} (hd : 0 < d) (B : Finset (List ℕ))
    (hB : ∀ l ∈ B, (∀ a ∈ l, 1 < a) ∧ l.prod = d) :
    B.card ≤ (ArithmeticFunction.cardFactors d) ^ (ArithmeticFunction.cardFactors d) := by
  let v := d.primeFactorsList.get
  have hv : ∀ i, (v i).Prime := fun i => Nat.prime_of_mem_primeFactorsList (List.get_mem _ i)
  apply allFactorListsBound v hv B
  intro l hl
  refine ⟨(hB l hl).1, ?_⟩
  rw [← List.prod_ofFn, List.ofFn_get, Nat.prod_primeFactorsList hd.ne']
  exact (hB l hl).2

#print axioms factorListLengthNat
#print axioms allFactorListsBoundNat
end AmicablePartitions
