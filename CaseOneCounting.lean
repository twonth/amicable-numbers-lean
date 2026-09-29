import CaseOneRange
import DyadicRanges

namespace AmicableCases
open AmicableManuscript AmicableCounting Filter
open scoped Topology

theorem caseOneCounting {e : ℝ} (he : 0 < e) (he1 : e < 1 / 10) :
    ∀ᶠ x : ℝ in atTop, ∀ F : Finset ℕ,
      (∀ n ∈ F, ∃ m R d p : ℕ, CaseOneData x e n m R d p) →
      (F.card : ℝ) ≤ x ^ (1 - e ^ 2 / 400) := by
  classical
  let a := e ^ 2 / 1200
  have ha : 0 < a := by dsimp [a]; positivity
  filter_upwards [caseOneRange he he1 ha, dyadicPairsAbsorb ha,
    AmicableAbsorption.constantLogAbsorb 10 ha,
    AmicableAbsorption.constantLogAbsorb 2 (show 0 < e ^ 2 / 20 by positivity),
    eventually_gt_atTop (1 : ℝ)] with x hrange hdyadic hlog htwo hx
  intro F hF
  choose! m R d p hw using hF
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos hx
  have hRbound : ∀ n ∈ F, (R n : ℝ) ≤ x * Real.log x := by
    intro n hn
    have hh : R n ≤ n := (Nat.le_mul_of_pos_left _ (hw n hn).mpos).trans_eq (hw n hn).eqn.symm
    exact (by exact_mod_cast hh : (R n : ℝ) ≤ n).trans (hw n hn).nbound
  have hblocks : ∀ j k : ℕ,
      ((F.filter (fun n => Nat.log 2 (p n) = j ∧ Nat.log 2 (R n) = k)).card : ℝ) ≤
        x ^ (1 - e ^ 2 / 200 + 2 * a) := by
    intro j k
    let B := F.filter (fun n => Nat.log 2 (p n) = j ∧ Nat.log 2 (R n) = k)
    by_cases hne : B.Nonempty
    · obtain ⟨n0, hn0⟩ := hne
      obtain ⟨hn0F, hp0, hR0⟩ := Finset.mem_filter.mp hn0
      let P : ℝ := 2 ^ j
      let U : ℝ := 2 ^ k
      have hU : 1 ≤ U := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hUpos : 0 < U := by linarith
      have hP : 0 ≤ P := by positivity
      have hranges : ∀ n ∈ B, ∃ m' R' d' p' : ℕ, CaseOneData x e n m' R' d' p' ∧
          P ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ 2 * P ∧ U ≤ (R' : ℝ) ∧ (R' : ℝ) ≤ 2 * U := by
        intro n hn
        obtain ⟨hnF, hpj, hRk⟩ := Finset.mem_filter.mp hn
        have hp := dyadicRange (hw n hnF).pprime.pos
        have hR := dyadicRange (hw n hnF).Rpos
        rw [hpj] at hp
        rw [hRk] at hR
        exact ⟨m n, R n, d n, p n, hw n hnF, hp.1, hp.2, hR.1, hR.2⟩
      have hc := hrange B P U hP hU hranges
      have hUlower : x ^ (e ^ 2 / 20) ≤ U := by
        have hRupper := (dyadicRange (hw n0 hn0F).Rpos).2
        rw [hR0] at hRupper
        have hRlower := (hw n0 hn0F).Rlower
        have htwo' : 2 ≤ x ^ (e ^ 2 / 20) := by nlinarith
        have hpow : x ^ (e ^ 2 / 10) = (x ^ (e ^ 2 / 20)) ^ 2 := by
          rw [← Real.rpow_mul_natCast hx0.le]
          congr 1
          ring
        rw [hpow] at hRlower
        dsimp [U]
        nlinarith
      have hU9 : 1 ≤ U ^ (9 / 10 : ℝ) := Real.one_le_rpow hU (by norm_num)
      have h2 : (2 : ℝ) ^ (9 / 10 : ℝ) ≤ 2 := by
        calc
          _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have hfactor : 1 + 2 * (2 * U) ^ (9 / 10 : ℝ) ≤ 5 * U ^ (9 / 10 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hUpos.le]
        nlinarith [Real.rpow_nonneg hUpos.le (9 / 10 : ℝ)]
      have hden : x ^ (e ^ 2 / 200) ≤ U ^ (1 / 10 : ℝ) := by
        have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hUlower (by norm_num : (0 : ℝ) ≤ 1 / 10)
        rw [← Real.rpow_mul hx0.le] at hh
        convert hh using 1 <;> ring
      have hpower : U ^ (9 / 10 : ℝ) / U = 1 / U ^ (1 / 10 : ℝ) := by
        conv_lhs => arg 2; rw [← Real.rpow_one U]
        rw [← Real.rpow_sub hUpos]
        norm_num
        rw [Real.rpow_neg hUpos.le, one_div]
      calc
        (B.card : ℝ) ≤ (x * Real.log x / U) * x ^ a * (5 * U ^ (9 / 10 : ℝ)) * 2 := by
          exact hc.trans (by gcongr)
        _ = (10 * Real.log x) * x * x ^ a / U ^ (1 / 10 : ℝ) := by
          have hh := hpower
          field_simp at hh ⊢
          nlinarith
        _ ≤ (10 * Real.log x) * x * x ^ a / x ^ (e ^ 2 / 200) :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hx0 _) hden
        _ ≤ x ^ a * x * x ^ a / x ^ (e ^ 2 / 200) := by gcongr; nlinarith
        _ = x ^ (1 - e ^ 2 / 200 + 2 * a) := by
          calc
            _ = x ^ a * x ^ (1 : ℝ) * x ^ a / x ^ (e ^ 2 / 200) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0]; congr 1; ring
    · have hB : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (B.card : ℝ) ≤ _
      rw [hB, Finset.card_empty, Nat.cast_zero]
      positivity
  have hc := dyadicPairsCount F p R (x * Real.log x) _
    (fun n hn => ⟨(hw n hn).pprime.pos, (hw n hn).Rpos⟩)
    (fun n hn => ⟨(hw n hn).pbound, hRbound n hn⟩) hblocks
  calc
    (F.card : ℝ) ≤ x ^ a * x ^ (1 - e ^ 2 / 200 + 2 * a) := hc.trans (by gcongr)
    _ = x ^ (1 - e ^ 2 / 400) := by
      rw [← Real.rpow_add hx0]
      congr 1
      dsimp [a]
      ring

#print axioms caseOneCounting
end AmicableCases
