import CountFibres

namespace AmicableCounting
open scoped BigOperators

theorem threeWitnessMultiplicity (F : Finset ℕ) (m d p : ℕ → ℕ) (M : ℕ) (T Q Z : ℝ)
    (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hm : ∀ n ∈ F, 0 < m n ∧ m n ≤ M)
    (hd : ∀ j ∈ F.image m,
      (((F.filter (fun n => m n = j)).image d).card : ℝ) ≤ T)
    (hp : ∀ j ∈ F.image m, ∀ k ∈ (F.filter (fun n => m n = j)).image d,
      (((F.filter (fun n => m n = j ∧ d n = k)).image p).card : ℝ) ≤ Q)
    (hfinal : ∀ j k q : ℕ,
      ((F.filter (fun n => m n = j ∧ d n = k ∧ p n = q)).card : ℝ) ≤ Z) :
    (F.card : ℝ) ≤ (M : ℝ) * T * Q * Z := by
  classical
  have hMcard : (F.image m).card ≤ M := by
    calc
      _ ≤ (Finset.Icc 1 M).card := Finset.card_le_card (by
        intro j hj
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_Icc.mpr ⟨(hm n hn).1, (hm n hn).2⟩)
      _ = M := by simp
  have hfirst := countImageFibres F m (T * (Q * Z)) (by
    intro j hj
    let Fj := F.filter (fun n => m n = j)
    have hsecond := countImageFibres Fj d (Q * Z) (by
      intro k hk
      let Fjk := Fj.filter (fun n => d n = k)
      have hid : Fjk = F.filter (fun n => m n = j ∧ d n = k) := by
        ext n; simp [Fjk, Fj, and_assoc]
      have hthird := countImageFibres Fjk p Z (by
        intro q hq
        have hid3 : Fjk.filter (fun n => p n = q) =
            F.filter (fun n => m n = j ∧ d n = k ∧ p n = q) := by
          ext n; simp [Fjk, Fj, and_assoc]
        rw [hid3]
        exact hfinal j k q)
      have hpcard := hp j hj k hk
      rw [← hid] at hpcard
      exact hthird.trans (mul_le_mul_of_nonneg_right hpcard hZ))
    exact hsecond.trans (mul_le_mul_of_nonneg_right (hd j hj) (mul_nonneg hQ hZ)))
  have hcast : ((F.image m).card : ℝ) ≤ M := by exact_mod_cast hMcard
  exact hfirst.trans ((mul_le_mul_of_nonneg_right hcast (by positivity)).trans_eq (by ring))

#print axioms threeWitnessMultiplicity
end AmicableCounting
