/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in vendor-licenses/PrimeGapsLib-LICENSE.
Authors: Axiom Math

Extracted Mertens upper-bound dependency for the amicable manuscript audit.
Sources and pinned upstream revision are recorded in vendor-provenance.json.
Only the needed statements have been extracted; compatibility changes are recorded there.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open ArithmeticFunction Real
open scoped Nat
namespace PrimeGaps

/-- Log-factorial identity: `∑_{1 ≤ n ≤ N} log n = ∑_{1 ≤ d ≤ N} Λ(d) · ⌊N/d⌋`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_zeta_eq_sum vonMangoldt N
  aesop

/-- Key floating bound: `|∑_{d≤N} Λd·⌊N/d⌋ − N·T| ≤ ψ(N)` where `T = ∑_{d≤N} Λd/d`. -/
theorem abs_sum_vonMangoldt_div_sub (N : ℕ) :
    |(∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ)) - (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d| ≤
      ∑ d ∈ Finset.Ioc 0 N, Λ d := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hbound : ∀ d ∈ Finset.Ioc 0 N, |Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d)| ≤ Λ d := by
    intro d hd
    obtain ⟨hd0, hdN⟩ := Finset.mem_Ioc.mp hd
    have hdpos : (0 : ℝ) < d := by positivity
    have hLnn : 0 ≤ Λ d := vonMangoldt_nonneg
    have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hdm : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = N := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.div_add_mod N d)
    have hmod : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N hd0
    have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdpos]
      linarith
    have heq : (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
    rw [heq, ← mul_sub, abs_mul, abs_of_nonneg hLnn]
    have habs : |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by grind
    exact mul_le_of_le_one_right hLnn habs
  calc |∑ d ∈ Finset.Ioc 0 N, (Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d))|
      ≤ ∑ d ∈ Finset.Ioc 0 N, |Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d := Finset.sum_le_sum hbound

/-- `∑_{n∈Ioc 0 N} Real.log n = Real.log (N !)`. -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = Real.log (N ! : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    grind

/-- Bounds on `∑_{n∈Ioc 0 N} log n`: within `N` of `N log N`, for `N ≥ 1`. -/
theorem abs_sum_log_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Ioc 0 N, Real.log n) - (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hNe : N ≠ 0 := by omega
  rw [sum_log_eq_log_factorial]
  have hup : Real.log (N ! : ℝ) ≤ (N : ℝ) * Real.log N := by
    rw [← sum_log_eq_log_factorial]
    calc ∑ n ∈ Finset.Ioc 0 N, Real.log n
        ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log N :=
          Finset.sum_le_sum fun n hn ↦ Real.log_le_log (mod_cast (Finset.mem_Ioc.mp hn).1)
            (mod_cast (Finset.mem_Ioc.mp hn).2)
      _ = (N : ℝ) * Real.log N := by aesop
  have hlow := Stirling.le_log_factorial_stirling hNe
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h2pi : 0 ≤ Real.log (2 * π) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  grind

/-- ψ-bound in the `Ioc 0 N` form: `∑_{d∈Ioc 0 N} Λ d ≤ (log 4 + 4)·N`. -/
theorem sum_vonMangoldt_Ioc_le (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have hpsi : Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Icc 0 N, Λ n := by
    simp [Chebyshev.psi_eq_sum_Icc]
  have hIcc : ∑ n ∈ Finset.Icc 0 N, Λ n = ∑ d ∈ Finset.Ioc 0 N, Λ d := by
    rw [show Finset.Icc 0 N = insert 0 (Finset.Ioc 0 N) from ?_]
    · exact Finset.sum_insert_of_eq_zero_if_notMem fun _ ↦ ArithmeticFunction.map_zero
    · grind
  have hle := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  grind

/-- **Integer von-Mangoldt Mertens:** `|T_N − log N| ≤ log 4 + 5` where
`T_N = ∑_{d∈Ioc 0 N} Λd/d`, for `N ≥ 1`. -/
theorem abs_sum_vonMangoldt_div_sub_log {N : ℕ} (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Ioc 0 N, Λ d / d) - Real.log N| ≤ Real.log 4 + 5 := by
  have hNpos : (0 : ℝ) < N := by positivity
  set T := ∑ d ∈ Finset.Ioc 0 N, Λ d / d with hT
  have hid := sum_log_eq_sum_vonMangoldt_mul_div N
  have hfloat := abs_sum_vonMangoldt_div_sub N
  rw [← hT] at hfloat
  have hpsi := sum_vonMangoldt_Ioc_le N
  have hstir := abs_sum_log_sub_le hN
  have hcomb : |(N : ℝ) * T - (N : ℝ) * Real.log N| ≤ (Real.log 4 + 5) * (N : ℝ) := by grind
  rw [← mul_sub, abs_mul, abs_of_pos hNpos] at hcomb
  have hcomb' : (N : ℝ) * |T - Real.log N| ≤ (N : ℝ) * (Real.log 4 + 5) := by grind
  exact le_of_mul_le_mul_left hcomb' hNpos

end PrimeGaps

open scoped Topology Interval
open ArithmeticFunction Finset Real
namespace AmicableMertens
/-- **Von Mangoldt average, coefficient exactly 1.**
`∑_{n ≤ x} Λ(n)/n ≤ log x + C₂` for an absolute constant `C₂`, all `x ≥ 2`; the
coefficient on `log x` is exactly `1`. Proved from the Mertens-type bound
`PrimeGaps.abs_sum_vonMangoldt_div_sub_log` at `N = ⌊x⌋₊`, together with
`log ⌊x⌋₊ ≤ log x`. -/
theorem sum_vonMangoldt_div_le : ∃ C₂ : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n ≤ Real.log x + C₂ := by
  refine ⟨Real.log 4 + 5, ?_⟩
  intro x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hN1
  have hkey := PrimeGaps.abs_sum_vonMangoldt_div_sub_log hN1
  rw [abs_le] at hkey
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
  linarith [hkey.2, Real.log_le_log hNpos hfloor]

/-- **Drop prime powers.** `∑_{p ≤ x} (log p)/p ≤ log x + C₃` for `x ≥ 2`.
Since `Λ(p) = log p` on primes and `Λ(n)/n ≥ 0`, the prime sum is dominated by the
full von Mangoldt average `∑_{n ≤ x} Λ(n)/n` (`sum_vonMangoldt_div_le`) via
`Finset.sum_le_sum_of_subset_of_nonneg`, so one may take `C₃ = C₂`. -/
theorem sum_log_div_prime_le : ∃ C₃ : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p ≤ Real.log x + C₃ := by
  obtain ⟨C₂, hC₂⟩ := sum_vonMangoldt_div_le
  refine ⟨C₂, fun x hx ↦ ?_⟩
  have hrw : ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p =
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Λ p / p :=
    Finset.sum_congr rfl fun p hp ↦ by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesBelow hp)]
  rw [hrw]
  have hsub : Nat.primesBelow (⌊x⌋₊ + 1) ⊆ Finset.Ioc 0 ⌊x⌋₊ := fun p hp ↦ by
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_Ioc.mpr ⟨hp.2.pos, Nat.lt_succ_iff.mp hp.1⟩
  have hnonneg : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      n ∉ Nat.primesBelow (⌊x⌋₊ + 1) → 0 ≤ Λ n / n :=
    fun n _ _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  calc ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Λ p / p
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ ≤ Real.log x + C₂ := hC₂ x hx

/-- A globally differentiable extension of `t ↦ (log t)⁻¹`: it agrees with `(log t)⁻¹` on
`[2, ∞)` and is continued below `2` by the tangent line at `2`. -/
private noncomputable def invLogExt (t : ℝ) : ℝ :=
  if t ≤ 2 then (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2) else (Real.log t)⁻¹

/-- The derivative of `invLogExt`: `-(t (log t)²)⁻¹` read at `max t 2`, so it is
`-(t (log t)²)⁻¹` above `2` and constant below. -/
private noncomputable def invLogExtDeriv (t : ℝ) : ℝ :=
  -(max t 2 * (Real.log (max t 2)) ^ 2)⁻¹

/-- `invLogExt` agrees with `(log t)⁻¹` on `[2, ∞)`. -/
private lemma invLogExt_eq_inv_log {t : ℝ} (ht : 2 ≤ t) : invLogExt t = (Real.log t)⁻¹ := by
  rcases eq_or_lt_of_le ht with h | h
  · simp only [invLogExt]; rw [if_pos (le_of_eq h.symm), ← h]; ring
  · simp only [invLogExt]; rw [if_neg (by linarith)]

/-- Above `2`, `invLogExtDeriv t` is `-(t (log t)²)⁻¹`. -/
private lemma invLogExtDeriv_of_two_lt {t : ℝ} (ht : 2 < t) :
    invLogExtDeriv t = -(t * (Real.log t) ^ 2)⁻¹ := by
  rw [invLogExtDeriv, max_eq_left ht.le]

/-- `t ↦ (log t)⁻¹` has derivative `-(t (log t)²)⁻¹` at every `t > 1`. -/
private lemma hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s ↦ (Real.log s)⁻¹) (-(t * (Real.log t) ^ 2)⁻¹) t := by
  refine (Real.hasDerivAt_inv_log (by linarith : (0 : ℝ) < t).ne' ht.ne'
    (by linarith : (-1 : ℝ) < t).ne').congr_deriv ?_
  rw [neg_div, neg_inj, div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- `invLogExtDeriv` is continuous: `max t 2` stays above `2`, where the logarithm is positive and
the denominator therefore nonzero. -/
private lemma continuous_invLogExtDeriv : Continuous invLogExtDeriv := by
  have hmax : ∀ t : ℝ, (2 : ℝ) ≤ max t 2 := fun t ↦ le_max_right _ _
  have hm : Continuous fun t : ℝ ↦ max t 2 := continuous_id.max continuous_const
  have hlog : Continuous fun t : ℝ ↦ Real.log (max t 2) :=
    hm.log fun t ↦ by linarith [hmax t]
  refine ((hm.mul (hlog.pow 2)).inv₀ fun t ↦ ?_).neg
  have hpos : 0 < Real.log (max t 2) := Real.log_pos (by linarith [hmax t])
  exact (mul_pos (by linarith [hmax t]) (pow_pos hpos 2)).ne'

/-- `invLogExt` is differentiable on all of `ℝ`, with derivative `invLogExtDeriv`. -/
private lemma hasDerivAt_invLogExt (y : ℝ) : HasDerivAt invLogExt (invLogExtDeriv y) y := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hne : ∀ y : ℝ, y ≠ 2 → HasDerivAt invLogExt (invLogExtDeriv y) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have hda : HasDerivAt (fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2))
          (-(2 * (Real.log 2) ^ 2)⁻¹) y := by
        have := ((hasDerivAt_id y).sub_const (2 : ℝ)).const_mul (-(2 * (Real.log 2) ^ 2)⁻¹)
        simpa using (this.const_add ((Real.log 2)⁻¹))
      have heq : invLogExt =ᶠ[𝓝 y]
          (fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2)) := by
        filter_upwards [eventually_lt_nhds hlt] with t ht
        simp only [invLogExt]; rw [if_pos (le_of_lt ht)]
      rw [invLogExtDeriv, max_eq_right hlt.le]
      exact hda.congr_of_eventuallyEq heq
    · have hd := hasDerivAt_inv_log (t := y) (by linarith)
      have heq : invLogExt =ᶠ[𝓝 y] (fun s ↦ (Real.log s)⁻¹) := by
        filter_upwards [eventually_gt_nhds hgt] with t ht
        simp only [invLogExt]; rw [if_neg (by linarith)]
      rw [invLogExtDeriv, max_eq_left hgt.le]
      exact hd.congr_of_eventuallyEq heq
  rcases eq_or_ne y 2 with rfl | hy
  · apply hasDerivAt_of_hasDerivAt_of_ne (fun z hz ↦ hne z hz)
    · have hcont_le : ContinuousWithinAt invLogExt (Set.Iic 2) 2 := by
        apply ContinuousWithinAt.congr
          (f := fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2))
        · fun_prop
        · intro t ht; simp only [invLogExt]; rw [if_pos (Set.mem_Iic.mp ht)]
        · simp only [invLogExt]; rw [if_pos le_rfl]
      have hcont_ge : ContinuousWithinAt invLogExt (Set.Ici 2) 2 := by
        apply ContinuousWithinAt.congr (f := fun t ↦ (Real.log t)⁻¹)
        · exact ((Real.continuousAt_log (by norm_num)).continuousWithinAt).inv₀ hl2
        · intro t ht; exact invLogExt_eq_inv_log (Set.mem_Ici.mp ht)
        · simp only [invLogExt]; rw [if_pos le_rfl]; ring
      have hu : ContinuousWithinAt invLogExt (Set.Iic 2 ∪ Set.Ici 2) 2 := hcont_le.union hcont_ge
      rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at hu
    · exact continuous_invLogExtDeriv.continuousAt
  · exact hne y hy

/-- **Abel/partial summation identity.** For `x ≥ e`, with partial sums
`A(t) = ∑_{p ≤ t} (log p)/p`, the inverse-prime sum is recovered by partial summation
against the C¹ weight `f(t) = 1/log t`:
  `∑_{p ≤ x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t (log t)²) dt`.
This applies `sum_mul_eq_sub_integral_mul` (`Mathlib.NumberTheory.AbelSummation`) with
weight `c k = if k.Prime then (log k)/k else 0`. Since `1/log t` is not differentiable
at `t ∈ {0, 1}`, it is replaced by a function `g` agreeing with `1/log t` on `[2, ∞)`
and differentiable on all of `[0, x]`; this is harmless because `A(t) = 0` for `t < 2`,
so the integrand vanishes where `g` and `1/log t` differ. -/
theorem abel_sum_inv_prime : ∀ x : ℝ, rexp 1 ≤ x →
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p =
        (∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p) / Real.log x + ∫ t in Set.Ioc (2 : ℝ) x,
              (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2) := by
  intro x hx
  have he2 : (2 : ℝ) < rexp 1 := by have := Real.exp_one_gt_d9; linarith
  have hx2 : (2 : ℝ) ≤ x := he2.le.trans hx
  have hxgt2 : (2 : ℝ) < x := he2.trans_le hx
  set g : ℝ → ℝ := invLogExt
  set dg : ℝ → ℝ := invLogExtDeriv
  set c : ℕ → ℝ := fun k ↦ if k.Prime then Real.log k / k else 0 with hcdef
  have hg_eq : ∀ t : ℝ, 2 ≤ t → g t = (Real.log t)⁻¹ := fun _ ht ↦ invLogExt_eq_inv_log ht
  have g_hasDeriv : ∀ y : ℝ, HasDerivAt g (dg y) y := hasDerivAt_invLogExt
  have hderiv_g : ∀ y, deriv g y = dg y := fun y ↦ (g_hasDeriv y).deriv
  have dg_cont : Continuous dg := continuous_invLogExtDeriv
  have hf' : MeasureTheory.IntegrableOn (deriv g) (Set.Icc 0 x) MeasureTheory.volume := by
    have hdgeq : deriv g = dg := funext hderiv_g
    rw [hdgeq]
    exact (dg_cont.continuousOn).integrableOn_compact isCompact_Icc
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) x, DifferentiableAt ℝ g t :=
    fun t _ ↦ (g_hasDeriv t).differentiableAt
  have hb : (0 : ℝ) ≤ x := by linarith
  have habel := sum_mul_eq_sub_integral_mul c hb hf hf'
  have recon : ∀ (m : ℕ) (v : ℕ → ℝ),
      ∑ k ∈ Finset.Icc 0 m, (if k.Prime then v k else 0) = ∑ p ∈ Nat.primesBelow (m + 1), v p := by
    intro m v
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
    exact ⟨fun h ↦ ⟨by omega, h.2⟩, fun h ↦ ⟨⟨Nat.zero_le _, by omega⟩, h.2⟩⟩
  have hAdisc : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p :=
    fun t ↦ by rw [hcdef]; exact recon ⌊t⌋₊ fun k ↦ Real.log k / k
  have hLHS : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, g ↑k * c k =
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p := by
    rw [← recon ⌊x⌋₊ (fun k ↦ (1 : ℝ) / k)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hcdef]; simp only
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      have hk2 : 2 ≤ k := hp.two_le
      have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      rw [hg_eq k hkr]
      have hlogk : Real.log k ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < (k : ℝ))).ne'
      field_simp
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hgx : g x = (Real.log x)⁻¹ := hg_eq x hx2
  have hInt : (∫ (t : ℝ) in Set.Ioc 0 x, deriv g t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = -
      ∫ t in Set.Ioc (2 : ℝ) x,
          (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2) := by
    have hrw : (∫ (t : ℝ) in Set.Ioc 0 x, deriv g t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        ∫ (t : ℝ) in Set.Ioc 0 x, dg t * (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t _; dsimp only; rw [hderiv_g, hAdisc t]
    rw [hrw]
    set A : ℝ → ℝ := fun t ↦ ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p with hAdef
    have hA0 : ∀ t, t < 2 → A t = 0 := by
      intro t ht
      rw [hAdef]; simp only
      apply Finset.sum_eq_zero
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      have hfloor : ⌊t⌋₊ ≤ 1 := by
        rcases lt_or_ge t 0 with h0 | h0
        · rw [Nat.floor_eq_zero.mpr (by linarith)]; omega
        · have := (Nat.floor_lt h0).mpr (by exact_mod_cast ht : t < ((2 : ℕ) : ℝ)); omega
      exact absurd hp.2.two_le (by omega)
    have hdg : ∀ t, 2 < t → dg t = -(t * (Real.log t) ^ 2)⁻¹ :=
      fun _ ht ↦ invLogExtDeriv_of_two_lt ht
    have hinter : Set.Ioc (0 : ℝ) x ∩ Set.Ioc (2 : ℝ) x = Set.Ioc (2 : ℝ) x := by
      rw [Set.inter_eq_right]; intro t ht; rw [Set.mem_Ioc] at ht ⊢; exact ⟨by linarith, ht.2⟩
    have step1 : (∫ t in Set.Ioc (0 : ℝ) x, dg t * A t) = ∫ t in Set.Ioc (0 : ℝ) x,
          (Set.Ioc (2 : ℝ) x).indicator (fun t ↦ -(A t / (t * (Real.log t) ^ 2))) t := by
      apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
      have hne : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ 2 := by
        rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with t htne hmem
      rw [Set.mem_Ioc] at hmem
      rcases lt_trichotomy t 2 with hlt | heq | hgt
      · rw [hA0 t hlt, mul_zero, Set.indicator_of_notMem]
        rw [Set.mem_Ioc]; rintro ⟨h, _⟩; linarith
      · exact absurd heq htne
      · rw [Set.indicator_of_mem (by rw [Set.mem_Ioc]; exact ⟨hgt, hmem.2⟩), hdg t hgt]
        field_simp
    rw [step1, MeasureTheory.setIntegral_indicator measurableSet_Ioc, hinter,
      MeasureTheory.integral_neg]
  rw [hLHS] at habel
  rw [habel, hgx, hInt, hAdisc x]
  ring

/-- On `[2, x]` the function `t ↦ k / (t (log t)ⁿ)` is continuous: the denominator is a product
of continuous factors and is bounded away from `0`, since `t ≥ 2` gives `log t > 0`. -/
private lemma continuousOn_const_div_mul_log_pow (k : ℝ) (n : ℕ) {x : ℝ} (hx2 : (2 : ℝ) ≤ x) :
    ContinuousOn (fun t ↦ k / (t * (Real.log t) ^ n)) ([[2, x]]) := by
  rw [Set.uIcc_of_le hx2]
  apply ContinuousOn.div continuousOn_const
  · apply continuousOn_id.mul
    apply ContinuousOn.pow
    exact (Real.continuousOn_log.mono (by
      intro t ht; simp only [Set.mem_Icc] at ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]))
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have h1 : (0 : ℝ) < t := by linarith [ht.1]
    have h2 : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity

/-- **Integral bound via the antiderivative `log log t`.** Using `A(t) ≤ log t + C₃`
(from `sum_log_div_prime_le`) and the antiderivatives `d/dt log log t = 1/(t log t)`
and `d/dt (-1/log t) = 1/(t (log t)²)`, the Abel integral of `A(t)/(t (log t)²)` over
`[2, x]` is bounded by `log log x` plus an absolute constant `C₄`, for `x ≥ e`:
  `∫_2^x A(t)/(t (log t)²) dt ≤ ∫_2^x (log t + C₃)/(t (log t)²) dt
     = (log log x - log log 2) + C₃ (1/log 2 - 1/log x)
     ≤ log log x + C₄`.
The two explicit integrals are evaluated by the Fundamental Theorem of Calculus; the
constant `C₄` is chosen existentially. -/
theorem abel_integral_bound (C₃ : ℝ)
    (hC₃ : ∀ x : ℝ, 2 ≤ x → ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p ≤ Real.log x + C₃) :
    ∃ C₄ : ℝ, ∀ x : ℝ, rexp 1 ≤ x → (∫ t in Set.Ioc (2 : ℝ) x,
          (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2)) ≤
        Real.log (Real.log x) + C₄ := by
  set A : ℝ → ℝ := fun t ↦ ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p
  have hAmeas : Measurable A := by
    have : A = (fun n : ℕ ↦ ∑ p ∈ Nat.primesBelow (n + 1), Real.log p / p) ∘ (fun t : ℝ ↦ ⌊t⌋₊) :=
      rfl
    rw [this]
    exact (measurable_from_nat).comp Nat.measurable_floor
  refine ⟨(max C₃ 0) / Real.log 2 - Real.log (Real.log 2), ?_⟩
  intro x hx
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2e : (2 : ℝ) ≤ rexp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans h2e hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (by positivity) hx
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set g : ℝ → ℝ := fun t ↦ 1 / (t * Real.log t) + C₃ / (t * (Real.log t) ^ 2) with hg
  have huicc : [[(2 : ℝ), x]] = Set.Icc 2 x := Set.uIcc_of_le hx2
  have hcont1 : ContinuousOn (fun t ↦ 1 / (t * Real.log t)) ([[2, x]]) := by
    simpa only [pow_one] using continuousOn_const_div_mul_log_pow 1 1 hx2
  have hcont2 : ContinuousOn (fun t ↦ C₃ / (t * (Real.log t) ^ 2)) ([[2, x]]) :=
    continuousOn_const_div_mul_log_pow C₃ 2 hx2
  have hgcont : ContinuousOn g ([[2, x]]) := hcont1.add hcont2
  have hgint : IntervalIntegrable g MeasureTheory.volume 2 x := hgcont.intervalIntegrable
  set f : ℝ → ℝ := fun t ↦ A t / (t * (Real.log t) ^ 2) with hf
  have hfmeas : Measurable f :=
    hAmeas.div (measurable_id.mul ((Real.measurable_log.comp measurable_id).pow_const 2))
  have hbound : ∀ t ∈ Set.Icc (2 : ℝ) x, f t ≤ g t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    have hAle : A t ≤ Real.log t + C₃ := hC₃ t ht.1
    change A t / (t * (Real.log t) ^ 2) ≤ 1 / (t * Real.log t) + C₃ / (t * (Real.log t) ^ 2)
    have hden : (0 : ℝ) < t * (Real.log t) ^ 2 := by positivity
    have e1 : 1 / (t * Real.log t) = Real.log t / (t * (Real.log t) ^ 2) := by field_simp
    rw [e1, ← add_div, div_le_div_iff_of_pos_right hden]
    linarith
  have hfnonneg : ∀ t ∈ Set.Icc (2 : ℝ) x, 0 ≤ f t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    have hAn : 0 ≤ A t := Finset.sum_nonneg fun p hp ↦ by
      have : (0 : ℝ) ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
      positivity
    change 0 ≤ A t / (t * (Real.log t) ^ 2)
    positivity
  have hfint : IntervalIntegrable f MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx2]
    have hginton : MeasureTheory.IntegrableOn g (Set.Ioc 2 x) MeasureTheory.volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx2]; exact hgint
    refine (hginton.mono' hfmeas.aestronglyMeasurable ?_)
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
    rw [Set.mem_Ioc] at ht
    have htmem : t ∈ Set.Icc (2 : ℝ) x := Set.mem_Icc.mpr ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg t htmem)]
    exact hbound t htmem
  rw [← intervalIntegral.integral_of_le hx2]
  calc ∫ t in (2 : ℝ)..x, f t
      ≤ ∫ t in (2 : ℝ)..x, g t := intervalIntegral.integral_mono_on hx2 hfint hgint hbound
    _ = (Real.log (Real.log x) - Real.log (Real.log 2)) +
          C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) := by
        rw [hg]
        rw [intervalIntegral.integral_add hcont1.intervalIntegrable hcont2.intervalIntegrable]
        congr 1
        · have hderiv : ∀ t ∈ [[(2 : ℝ), x]],
              HasDerivAt (fun s ↦ Real.log (Real.log s)) (1 / (t * Real.log t)) t := by
            intro t ht
            rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
            have htne : t ≠ 0 := by linarith [ht.1]
            have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
            refine (Real.hasDerivAt_log_log htne (by linarith [ht.1] : (1 : ℝ) < t).ne'
              (by linarith [ht.1] : (-1 : ℝ) < t).ne').congr_deriv ?_
            field_simp
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont1.intervalIntegrable]
        · have hderiv : ∀ t ∈ [[(2 : ℝ), x]],
              HasDerivAt (fun s ↦ -(Real.log s)⁻¹) (1 / (t * (Real.log t) ^ 2)) t := by
            intro t ht
            rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
            have htne : t ≠ 0 := by linarith [ht.1]
            have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
            have h2 := Real.hasDerivAt_inv_log htne (by linarith [ht.1] : t ≠ 1)
              (by linarith [ht.1] : t ≠ -1)
            refine h2.neg.congr_deriv ?_
            rw [neg_div, neg_neg]
            field_simp [htne, pow_ne_zero 2 hlt]
          have hcont2' : ContinuousOn (fun t ↦ 1 / (t * (Real.log t) ^ 2)) ([[2, x]]) :=
            continuousOn_const_div_mul_log_pow 1 2 hx2
          have key : ∫ t in (2 : ℝ)..x, 1 / (t * (Real.log t) ^ 2) =
              (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
              hcont2'.intervalIntegrable]; ring
          rw [show (fun t ↦ C₃ / (t * (Real.log t) ^ 2)) =
            (fun t ↦ C₃ * (1 / (t * (Real.log t) ^ 2))) from by funext t; ring]
          rw [intervalIntegral.integral_const_mul, key]
    _ ≤ Real.log (Real.log x) + (max C₃ 0 / Real.log 2 - Real.log (Real.log 2)) := by
        have hxinv : (0 : ℝ) < (Real.log x)⁻¹ := by positivity
        have hdiff : (Real.log 2)⁻¹ - (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := by linarith
        have hdiffpos : (0 : ℝ) ≤ (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
          have hle : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := by
            have hlog2x : Real.log 2 ≤ Real.log x := by
              apply Real.log_le_log (by norm_num)
              exact le_trans h2e hx
            gcongr
          linarith
        have hCmax : C₃ ≤ max C₃ 0 := le_max_left _ _
        have hmaxnn : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
        have hterm : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ max C₃ 0 / Real.log 2 := by
          rcases lt_or_ge C₃ 0 with hC | hC
          · have hle0 : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_lt hC) hdiffpos
            have hge0 : (0 : ℝ) ≤ max C₃ 0 / Real.log 2 := by positivity
            linarith
          · have h1' : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ C₃ * (Real.log 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hdiff hC
            have h2' : C₃ * (Real.log 2)⁻¹ ≤ max C₃ 0 * (Real.log 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hCmax (le_of_lt (by positivity))
            rw [div_eq_mul_inv]; linarith
        linarith

/-- **Endpoint reconciliation for `2 ≤ z ≤ e`.** On `[2, e]` we have `⌊z⌋₊ = 2` (since
`e < 3`), so `Nat.primesBelow (⌊z⌋₊ + 1) = {2}` and the sum is exactly `1/2`. As
`log log z` is increasing and minimized at `z = 2` on this range, the bound
`∑_{p ≤ z} 1/p ≤ log log z + B₀` holds with the absolute constant
`B₀ = 1/2 - log log 2` (note `log log 2 < 0`). -/
theorem sum_inv_prime_le_endpoint : ∃ B₀ : ℝ, ∀ z : ℝ, 2 ≤ z → z ≤ rexp 1 →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₀ := by
  refine ⟨1 / 2 - Real.log (Real.log 2), ?_⟩
  intro z hz2 hze
  have hz3 : z < 3 := by have := Real.exp_one_lt_d9; linarith
  have hfloor : ⌊z⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast hz2, by push_cast; linarith⟩
  rw [hfloor]
  have hprimes : Nat.primesBelow 3 = {2} := by decide
  rw [hprimes, Finset.sum_singleton]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
  have hloglog : Real.log (Real.log 2) ≤ Real.log (Real.log z) := Real.log_le_log hlog2pos hlogle
  norm_num
  linarith

/-- **Mertens' second theorem (upper bound).** `∑_{p ≤ z} 1/p ≤ log log z + B₁` for an
absolute constant `B₁`, valid for all `z ≥ 2`; the coefficient on `log log z` is exactly
`1`. For `z ≥ e` this combines the Abel identity (`abel_sum_inv_prime`) with the integral
bound (`abel_integral_bound`); the endpoint range `[2, e]` is handled by
`sum_inv_prime_le_endpoint`. -/
theorem sum_inv_prime_le : ∃ B₁ : ℝ, ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₁ := by
  obtain ⟨C₃, hC₃⟩ := sum_log_div_prime_le
  obtain ⟨B₀, hB₀⟩ := sum_inv_prime_le_endpoint
  obtain ⟨C₄, hintb⟩ := abel_integral_bound C₃ hC₃
  refine ⟨max (1 + max C₃ 0 + C₄) B₀, ?_⟩
  intro z hz
  rcases le_or_gt (rexp 1) z with hze | hze
  · have hlogz : (1 : ℝ) ≤ Real.log z := by
      have : Real.log (rexp 1) ≤ Real.log z := Real.log_le_log (Real.exp_pos 1) hze
      rwa [Real.log_exp] at this
    have hAle : (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) ≤ Real.log z + C₃ :=
      hC₃ z (by linarith [Real.add_one_le_exp (1 : ℝ)] )
    have hAnn : 0 ≤ (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) :=
      Finset.sum_nonneg fun p hp ↦ by
        have : (0 : ℝ) ≤ Real.log p :=
          Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
        positivity
    have hterm1 : (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) / Real.log z ≤
        1 + max C₃ 0 := by
      rw [div_le_iff₀ (by linarith)]
      have hmax : C₃ ≤ max C₃ 0 := le_max_left _ _
      have hmax0 : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
      nlinarith [hAle, hAnn, hlogz, hmax, hmax0]
    have hident := abel_sum_inv_prime z hze
    have hintbz := hintb z hze
    rw [hident]
    calc (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) / Real.log z +
            (∫ t in Set.Ioc (2 : ℝ) z,
                  (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2)) ≤
          (1 + max C₃ 0) + (Real.log (Real.log z) + C₄) := add_le_add hterm1 hintbz
      _ ≤ Real.log (Real.log z) + (1 + max C₃ 0 + C₄) := by linarith
      _ ≤ Real.log (Real.log z) + max (1 + max C₃ 0 + C₄) B₀ := by
            have := le_max_left (1 + max C₃ 0 + C₄) B₀; linarith
  · have := hB₀ z hz (le_of_lt hze)
    calc ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₀ := this
      _ ≤ Real.log (Real.log z) + max (1 + max C₃ 0 + C₄) B₀ := by
          have := le_max_right (1 + max C₃ 0 + C₄) B₀; linarith


#print axioms sum_inv_prime_le
#print axioms PrimeGaps.abs_sum_vonMangoldt_div_sub_log
end AmicableMertens
