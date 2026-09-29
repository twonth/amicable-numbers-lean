import CaseOneCount
import CountMultiplicity
import DivisorBound

namespace AmicableCases
open AmicableManuscript AmicableCounting Filter
open scoped Topology

structure CaseOneData (x e : ℝ) (n m R d p : ℕ) : Prop where
  mpos : 0 < m
  Rpos : 0 < R
  eqn : n = m * R
  nbound : (n : ℝ) ≤ x * Real.log x
  pprime : p.Prime
  pbound : (p : ℝ) ≤ x * Real.log x
  plower : x ^ (e ^ 2) ≤ (p : ℝ)
  Rlower : x ^ (e ^ 2 / 10) < (R : ℝ)
  coprime : m.Coprime R
  crossR : R.Coprime (s n)
  crossp : p.Coprime n
  partner : p ∣ s n
  types : (R.Prime ∧ R < p) ∨ (R : ℝ) ≤ x ^ (e ^ 2 / 5)
  dpos : 0 < d
  dm : d ∣ sigma m
  dp : d ∣ p + 1
  dsize : (p : ℝ) / (R : ℝ) ^ (9 / 10 : ℝ) < d

theorem caseOneRange {e a : ℝ} (he : 0 < e) (he1 : e < 1 / 10) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, ∀ (F : Finset ℕ) (P U : ℝ), 0 ≤ P → 1 ≤ U →
      (∀ n ∈ F, ∃ m R d p : ℕ, CaseOneData x e n m R d p ∧
        P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P ∧ U ≤ (R : ℝ) ∧ (R : ℝ) ≤ 2 * U) →
      (F.card : ℝ) ≤ (x * Real.log x / U) * x ^ a *
        (1 + 2 * (2 * U) ^ (9 / 10 : ℝ)) * 2 := by
  classical
  filter_upwards [caseOneRCount he he1, AmicableDivisors.sigmaDivisorCountUniform ha,
    eventually_gt_atTop (1 : ℝ)] with x hRcount hdiv hx
  intro F P U hP hU hF
  choose! m R d p hw hranges using hF
  let M := ⌊x * Real.log x / U⌋₊
  have hU0 : 0 < U := by linarith
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have hmX : ∀ n ∈ F, (m n : ℝ) ≤ x * Real.log x := by
    intro n hn
    have hh : m n ≤ n := (Nat.le_mul_of_pos_right _ (hw n hn).Rpos).trans_eq (hw n hn).eqn.symm
    exact (by exact_mod_cast hh : (m n : ℝ) ≤ n).trans (hw n hn).nbound
  have hmM : ∀ n ∈ F, 0 < m n ∧ m n ≤ M := by
    intro n hn
    refine ⟨(hw n hn).mpos, Nat.le_floor ?_⟩
    apply (le_div_iff₀ hU0).mpr
    have heq : (n : ℝ) = (m n : ℝ) * R n := by exact_mod_cast (hw n hn).eqn
    have hh := mul_le_mul_of_nonneg_left (hranges n hn).2.2.1 (Nat.cast_nonneg (m n))
    nlinarith [(hw n hn).nbound]
  have hdcount : ∀ j ∈ F.image m,
      (((F.filter (fun n => m n = j)).image d).card : ℝ) ≤ x ^ a := by
    intro j hj
    obtain ⟨n0, hn0, rfl⟩ := Finset.mem_image.mp hj
    have hspos : 0 < sigma (m n0) := by rw [sigma_eq_s_add_self]; have := (hw n0 hn0).mpos; omega
    have hsub : (F.filter (fun n => m n = m n0)).image d ⊆ (sigma (m n0)).divisors := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hnF, heqm⟩ := Finset.mem_filter.mp hn
      exact Nat.mem_divisors.mpr ⟨heqm ▸ (hw n hnF).dm, hspos.ne'⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hdiv _ (hmX n0 hn0))
  have hpcount : ∀ j ∈ F.image m, ∀ k ∈ (F.filter (fun n => m n = j)).image d,
      (((F.filter (fun n => m n = j ∧ d n = k)).image p).card : ℝ) ≤
        1 + 2 * (2 * U) ^ (9 / 10 : ℝ) := by
    intro j hj k hk
    obtain ⟨n0, hn0, heq0⟩ := Finset.mem_image.mp hk
    have hn0F := (Finset.mem_filter.mp hn0).1
    have hdpos : 0 < k := heq0 ▸ (hw n0 hn0F).dpos
    have hdsize : P / (2 * U) ^ (9 / 10 : ℝ) ≤ (k : ℝ) := by
      have hlow := (hw n0 hn0F).dsize
      have hRpos : (0 : ℝ) < R n0 := by exact_mod_cast (hw n0 hn0F).Rpos
      have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hRpos _)).mp hlow
      have hpR := Real.rpow_le_rpow hRpos.le (hranges n0 hn0F).2.2.2 (by norm_num : (0 : ℝ) ≤ 9 / 10)
      have hm := mul_le_mul_of_nonneg_left hpR (Nat.cast_nonneg (d n0))
      apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < 2 * U) _)).mpr
      rw [← heq0]
      nlinarith [(hranges n0 hn0F).1]
    apply caseOnePrimeCount _ hP hU hdpos hdsize
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hnF, hmj, hdk⟩ := Finset.mem_filter.mp hn
    exact ⟨(hranges n hnF).2.1, hdk ▸ (hw n hnF).dp⟩
  have hfinal : ∀ j k q : ℕ,
      ((F.filter (fun n => m n = j ∧ d n = k ∧ p n = q)).card : ℝ) ≤ 2 := by
    intro j k q
    let B := F.filter (fun n => m n = j ∧ d n = k ∧ p n = q)
    by_cases hne : B.Nonempty
    · obtain ⟨n0, hn0⟩ := hne
      obtain ⟨hn0F, hm0, hd0, hp0⟩ := Finset.mem_filter.mp hn0
      have hinj : Set.InjOn R B := by
        intro n1 hn1 n2 hn2 heq
        obtain ⟨hn1F, hm1, _, _⟩ := Finset.mem_filter.mp hn1
        obtain ⟨hn2F, hm2, _, _⟩ := Finset.mem_filter.mp hn2
        rw [(hw n1 hn1F).eqn, (hw n2 hn2F).eqn, hm1, hm2, heq]
      have hh := hRcount j q (B.image R) (hp0 ▸ (hw n0 hn0F).pprime)
        (hp0 ▸ (hw n0 hn0F).plower) (by
          intro S hS
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
          obtain ⟨hnF, hmj, hdk, hpq⟩ := Finset.mem_filter.mp hn
          have heqn : n = j * R n := by simpa only [hmj] using (hw n hnF).eqn
          refine ⟨(hw n hnF).Rpos, hmj ▸ (hw n hnF).coprime, ?_, ?_, ?_, ?_⟩
          · simpa only [← heqn, hpq] using (hw n hnF).crossp
          · simpa only [← heqn] using (hw n hnF).crossR
          · simpa only [← heqn, hpq] using (hw n hnF).partner
          · simpa only [hpq] using (hw n hnF).types)
      rw [Finset.card_image_of_injOn hinj] at hh
      exact_mod_cast hh
    · have hB := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [show F.filter (fun n => m n = j ∧ d n = k ∧ p n = q) = B from rfl, hB,
        Finset.card_empty, Nat.cast_zero]
      norm_num
  have hc := threeWitnessMultiplicity F m d p M (x ^ a)
    (1 + 2 * (2 * U) ^ (9 / 10 : ℝ)) 2 (by positivity) (by positivity) (by norm_num)
    hmM hdcount hpcount hfinal
  exact hc.trans (by gcongr; exact Nat.floor_le (by positivity))

#print axioms caseOneRange
end AmicableCases
