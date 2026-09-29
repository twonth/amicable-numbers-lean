import GcdCounting
import OmegaTail
import PartialSummation
import AsymptoticAbsorption

namespace AmicableGcdCounting
open AmicableManuscript Filter
open scoped Topology BigOperators

theorem divisorMultipleFamilyCount (F D : Finset ℕ) (N : ℕ)
    (hD : ∀ d ∈ D, 0 < d)
    (hF : ∀ n ∈ F, 0 < n ∧ n ≤ N ∧ ∃ d ∈ D, d ∣ n) :
    (F.card : ℝ) ≤ (N : ℝ) * ∑ d ∈ D, (1 : ℝ) / d := by
  classical
  choose! d hd hddiv using fun n hn => (hF n hn).2.2
  have hsplit := Finset.sum_fiberwise_of_maps_to hd (fun _ : ℕ => (1 : ℝ))
  calc
    (F.card : ℝ) = ∑ a ∈ D, ((F.filter (fun n => d n = a)).card : ℝ) := by simpa using hsplit.symm
    _ ≤ ∑ a ∈ D, (N : ℝ) / a := by
      apply Finset.sum_le_sum
      intro a ha
      apply AmicableSigmaCounting.multiplesCard _ N a (hD a ha)
      intro n hn
      obtain ⟨hnF, hda⟩ := Finset.mem_filter.mp hn
      exact ⟨(hF n hnF).1, (hF n hnF).2.1, hda ▸ hddiv n hnF⟩
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

theorem manyPrimeDivisorCount {c : ℝ} (hc : 0 < c) :
    ∀ᶠ A : ℝ in atTop, ∀ (N : ℕ) (F : Finset ℕ),
      (∀ n ∈ F, 0 < n ∧ n ≤ N ∧ ∃ d : ℕ, d ∣ n ∧ 0 < d ∧ (d : ℝ) ≤ A ∧
        c * Real.log A / Real.log (Real.log A) ≤ (d.primeFactors.card : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) * A ^ (-c / 3) := by
  classical
  filter_upwards [AmicableOmega.omegaTailUniform hc,
    AmicableAbsorption.dyadicCountAbsorb (by linarith : 0 < c / 6),
    eventually_ge_atTop (2 : ℝ)] with A htail habs hA
  intro N F hF
  choose! d hddiv hdpos hdA hdomega using fun n hn => (hF n hn).2.2
  let D := F.image d
  have hD : ∀ a ∈ D, 0 < a ∧ (a : ℝ) ≤ A ∧
      c * Real.log A / Real.log (Real.log A) ≤ (a.primeFactors.card : ℝ) := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨hdpos n hn, hdA n hn, hdomega n hn⟩
  have hpre : ∀ T : ℕ, 1 ≤ T → ((D.filter (· ≤ T)).card : ℝ) ≤ A ^ (-c / 2) * T := by
    intro T hT
    by_cases hTA : (T : ℝ) ≤ A
    · have hh := htail T (D.filter (· ≤ T)) hTA (by
        intro a ha
        obtain ⟨haD, haT⟩ := Finset.mem_filter.mp ha
        exact ⟨(hD a haD).1, haT, (hD a haD).2.2⟩)
      simpa only [mul_comm] using hh
    · have hh := htail ⌊A⌋₊ D (Nat.floor_le (by linarith : 0 ≤ A)) (by
        intro a ha
        exact ⟨(hD a ha).1, Nat.le_floor (hD a ha).2.1, (hD a ha).2.2⟩)
      have hTfloor : (⌊A⌋₊ : ℝ) ≤ T := (Nat.floor_le (by linarith : 0 ≤ A)).trans (le_of_not_ge hTA)
      have hcard : ((D.filter (· ≤ T)).card : ℝ) ≤ D.card := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      exact hcard.trans (hh.trans (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hTfloor (Real.rpow_nonneg (by linarith : 0 ≤ A) (-c / 2))))
  have hrec := AmicablePartialSummation.reciprocalFromCount D ⌊A⌋₊ (A ^ (-c / 2))
    (Real.rpow_nonneg (by linarith) _) (fun a ha => ⟨(hD a ha).1, Nat.le_floor (hD a ha).2.1⟩) hpre
  have hrec' : ∑ a ∈ D, (1 : ℝ) / a ≤ A ^ (-c / 3) := by
    have hh := mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg (by linarith : 0 ≤ A) (-c / 2))
    have hid : A ^ (-c / 2) * A ^ (c / 6) = A ^ (-c / 3) := by
      rw [← Real.rpow_add (by linarith : 0 < A)]
      congr 1
      ring
    rw [hid] at hh
    exact hrec.trans (by convert hh using 1 <;> ring)
  have hcount := divisorMultipleFamilyCount F D N (fun a ha => (hD a ha).1) (by
    intro n hn
    exact ⟨(hF n hn).1, (hF n hn).2.1, d n, Finset.mem_image_of_mem d hn, hddiv n hn⟩)
  exact hcount.trans (mul_le_mul_of_nonneg_left hrec' (Nat.cast_nonneg N))

#print axioms divisorMultipleFamilyCount
#print axioms manyPrimeDivisorCount
end AmicableGcdCounting
