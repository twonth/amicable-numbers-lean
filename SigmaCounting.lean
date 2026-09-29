import FactorizationCounting
import WeightArithmetic
import PrimeReciprocals

namespace AmicableSigmaCounting
open scoped BigOperators
open AmicableManuscript

/-- A factorization of d, together with the associated distinct prime factors of V. -/
def Witness (d V : ℕ) (l : List ℕ) : Prop :=
  (∀ a ∈ l, 1 < a) ∧ l.prod = d ∧
  ∃ q : Fin l.length → ℕ, (∀ i, (q i).Prime ∧ l.get i ∣ q i + 1 ∧ q i ≤ V) ∧
    (∏ i, q i) ∣ V

theorem existsWitness {d V : ℕ} (hd : 0 < d) (hV : Squarefree V) (hdiv : d ∣ sigma V) :
    ∃ l : List ℕ, Witness d V l := by
  classical
  rw [AmicableWeight.sigma_squarefree hV] at hdiv
  obtain ⟨e, he, heprod⟩ := AmicableAllocation.distributeDivisor V.primeFactors (fun q => q + 1) hdiv
  let T := V.primeFactors.filter (fun q => e q ≠ 1)
  have hepos : ∀ q ∈ V.primeFactors, 0 < e q := by
    intro q hq
    have hh := he q hq
    exact Nat.pos_of_dvd_of_pos hh (by omega)
  let E : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let a := fun i : Fin (Fintype.card T) => e (E i).val
  let q := fun i : Fin (Fintype.card T) => (E i).val
  have haprod : ∏ i, a i = d := by
    rw [show (∏ i, a i) = ∏ t : T, e t.val from E.prod_comp (fun t : T => e t.val)]
    change (∏ t ∈ T.attach, e t.val) = d
    rw [Finset.prod_attach T e]
    simpa [T, Finset.prod_filter_ne_one] using heprod
  have haq : ∀ i, 1 < a i ∧ (q i).Prime ∧ a i ∣ q i + 1 ∧ q i ≤ V := by
    intro i
    have ht := (E i).property
    obtain ⟨hpf, hne⟩ := Finset.mem_filter.mp ht
    exact ⟨by have := hepos _ hpf; dsimp [a]; omega,
      Nat.prime_of_mem_primeFactors hpf, he _ hpf,
      Nat.le_of_dvd (Nat.pos_of_ne_zero hV.ne_zero) (Nat.dvd_of_mem_primeFactors hpf)⟩
  have hqprod : (∏ i, q i) ∣ V := by
    rw [show (∏ i, q i) = ∏ t : T, t.val from E.prod_comp (fun t : T => t.val)]
    change (∏ t ∈ T.attach, t.val) ∣ V
    rw [Finset.prod_attach T (fun p : ℕ => p)]
    exact (Finset.prod_dvd_prod_of_subset T V.primeFactors (fun p : ℕ => p) (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd V)
  refine ⟨List.ofFn a, ?_⟩
  unfold Witness
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact (haq i).1
  · rw [List.prod_ofFn]
    exact haprod
  · let E' : Fin (List.ofFn a).length ≃ Fin (Fintype.card T) := finCongr List.length_ofFn
    refine ⟨fun i => q (E' i), ?_, ?_⟩
    · intro i
      have hg : (List.ofFn a).get i = a (E' i) := List.get_ofFn a i
      rw [hg]
      exact (haq (E' i)).2
    · rw [E'.prod_comp q]
      exact hqprod

theorem multiplesCard (F : Finset ℕ) (N d : ℕ) (hd : 0 < d)
    (hF : ∀ n ∈ F, 0 < n ∧ n ≤ N ∧ d ∣ n) :
    (F.card : ℝ) ≤ (N : ℝ) / d := by
  classical
  have hsub : F ⊆ (Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (hF n hn).2.1; omega),
      (hF n hn).1.ne', (hF n hn).2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_multiples'] at hcard
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  exact (Nat.cast_le.mpr hcard).trans hdiv

theorem fixedFactorizationCount (F : Finset ℕ) (N M : ℕ) (l : List ℕ)
    (hF : ∀ V ∈ F, 0 < V ∧ V ≤ N ∧
      ∃ q : Fin l.length → ℕ, (∀ i, (q i).Prime ∧ l.get i ∣ q i + 1 ∧ q i ≤ M) ∧
        (∏ i, q i) ∣ V) :
    (F.card : ℝ) ≤ (N : ℝ) * ∏ i : Fin l.length,
      ∑ p ∈ (Finset.range (M + 1)).filter (fun p => p.Prime ∧ l.get i ∣ p + 1), (1 : ℝ) / p := by
  classical
  let P := fun i : Fin l.length => (Finset.range (M + 1)).filter (fun p => p.Prime ∧ l.get i ∣ p + 1)
  choose! q hq hqdiv using fun V hV => (hF V hV).2.2
  have hmaps : ∀ V ∈ F, q V ∈ Fintype.piFinset P := by
    intro V hV
    simp only [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (hq V hV i).2.2; omega),
      (hq V hV i).1, (hq V hV i).2.1⟩
  have hsplit := Finset.sum_fiberwise_of_maps_to hmaps (fun _ : ℕ => (1 : ℝ))
  calc
    (F.card : ℝ) = ∑ f ∈ Fintype.piFinset P, ((F.filter (fun V => q V = f)).card : ℝ) := by
      simpa using hsplit.symm
    _ ≤ ∑ f ∈ Fintype.piFinset P, (N : ℝ) / ∏ i, (f i : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      have hfP : ∀ i, f i ∈ P i := Fintype.mem_piFinset.mp hf
      have hpos : 0 < ∏ i, f i := Finset.prod_pos (fun i _ =>
        (Finset.mem_filter.mp (hfP i)).2.1.pos)
      simpa only [Nat.cast_prod] using multiplesCard (F.filter (fun V => q V = f)) N (∏ i, f i) hpos (by
        intro V hV
        obtain ⟨hVF, hqf⟩ := Finset.mem_filter.mp hV
        exact ⟨(hF V hVF).1, (hF V hVF).2.1, hqf ▸ hqdiv V hVF⟩)
    _ = _ := by
      rw [Finset.prod_univ_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.prod_div_distrib]
      simp [div_eq_mul_inv]

#print axioms existsWitness
#print axioms multiplesCard
#print axioms fixedFactorizationCount
end AmicableSigmaCounting

