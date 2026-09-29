import ManuscriptArithmetic

namespace AmicableCounting
open scoped BigOperators

theorem countFibres {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (M : Finset β) (f : α → β) (B : ℝ)
    (hmap : ∀ n ∈ F, f n ∈ M)
    (hbound : ∀ m ∈ M, ((F.filter (fun n => f n = m)).card : ℝ) ≤ B) :
    (F.card : ℝ) ≤ (M.card : ℝ) * B := by
  have hid := Finset.sum_fiberwise_of_maps_to hmap (fun _ : α => (1 : ℝ))
  calc
    (F.card : ℝ) = ∑ m ∈ M, ((F.filter (fun n => f n = m)).card : ℝ) := by
      simpa using hid.symm
    _ ≤ ∑ _ ∈ M, B := Finset.sum_le_sum hbound
    _ = _ := by simp

theorem countImageFibres {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (f : α → β) (B : ℝ)
    (hbound : ∀ m ∈ F.image f, ((F.filter (fun n => f n = m)).card : ℝ) ≤ B) :
    (F.card : ℝ) ≤ ((F.image f).card : ℝ) * B :=
  countFibres F (F.image f) f B (fun n hn => Finset.mem_image_of_mem f hn) hbound

/-- Count m, then d, then V, with reconstruction giving uniqueness in each final fibre. -/
theorem threeWitnessCount (F : Finset ℕ) (m d V : ℕ → ℕ) (M : ℕ) (T Q : ℝ)
    (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (hm : ∀ n ∈ F, 0 < m n ∧ m n ≤ M)
    (hd : ∀ j ∈ F.image m,
      (((F.filter (fun n => m n = j)).image d).card : ℝ) ≤ T)
    (hV : ∀ j ∈ F.image m, ∀ k ∈ (F.filter (fun n => m n = j)).image d,
      (((F.filter (fun n => m n = j ∧ d n = k)).image V).card : ℝ) ≤ Q)
    (hunique : ∀ n1 ∈ F, ∀ n2 ∈ F, m n1 = m n2 → V n1 = V n2 → n1 = n2) :
    (F.card : ℝ) ≤ (M : ℝ) * T * Q := by
  classical
  have hMcard : (F.image m).card ≤ M := by
    calc
      _ ≤ (Finset.Icc 1 M).card := Finset.card_le_card (by
        intro j hj
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_Icc.mpr ⟨hm n hn |>.1, hm n hn |>.2⟩)
      _ = M := by simp
  have hfirst := countImageFibres F m (T * Q) (by
    intro j hj
    let Fj := F.filter (fun n => m n = j)
    have hsecond := countImageFibres Fj d Q (by
      intro k hk
      let Fjk := Fj.filter (fun n => d n = k)
      have hid : Fjk = F.filter (fun n => m n = j ∧ d n = k) := by
        ext n; simp [Fjk, Fj, and_assoc]
      have hinj : Set.InjOn V Fjk := by
        intro n1 hn1 n2 hn2 heq
        have h1 := Finset.mem_filter.mp hn1
        have h2 := Finset.mem_filter.mp hn2
        have hh1 := Finset.mem_filter.mp h1.1
        have hh2 := Finset.mem_filter.mp h2.1
        exact hunique n1 hh1.1 n2 hh2.1 (hh1.2.trans hh2.2.symm) heq
      have hh := hV j hj k hk
      rw [← hid, Finset.card_image_of_injOn hinj] at hh
      exact hh)
    exact hsecond.trans (mul_le_mul_of_nonneg_right (hd j hj) hQ))
  have hcast : ((F.image m).card : ℝ) ≤ M := by exact_mod_cast hMcard
  exact hfirst.trans ((mul_le_mul_of_nonneg_right hcast (mul_nonneg hT hQ)).trans_eq (by ring))

#print axioms countFibres
#print axioms countImageFibres
#print axioms threeWitnessCount
end AmicableCounting
