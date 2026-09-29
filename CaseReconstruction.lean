import SigmaUniform

namespace AmicableCases
open AmicableManuscript Filter
open scoped Topology

theorem primeReconstruction {m p R1 R2 : ℕ} (hp : p.Prime)
    (hR1 : R1.Prime) (hR2 : R2.Prime)
    (hm1 : R1.Coprime m) (hm2 : R2.Coprime m)
    (hpm : p.Coprime m) (hd1 : p ∣ s (m * R1)) (hd2 : p ∣ s (m * R2))
    (hsmall1 : R1 < p) (hsmall2 : R2 < p) : R1 = R2 := by
  have heq1 : s (m * R1) = R1 * s m + sigma m := by
    rw [Nat.mul_comm]; exact s_mul_prime hR1 hm1
  have heq2 : s (m * R2) = R2 * s m + sigma m := by
    rw [Nat.mul_comm]; exact s_mul_prime hR2 hm2
  have hcop : p.Coprime (s m) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hps
    have hpsig : p ∣ sigma m := by
      rw [heq1] at hd1
      exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hps R1)).mpr hd1
    have hpmm : p ∣ m := by
      rw [sigma_eq_s_add_self] at hpsig
      exact (Nat.dvd_add_iff_right hps).mpr hpsig
    exact hp.not_dvd_one (hpm.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hpmm)
  have hc : Int.gcd (p : ℤ) (s m : ℤ) = 1 := by simpa [Int.gcd] using hcop
  have hdiv1 : (p : ℤ) ∣ (s m : ℤ) * R1 + sigma m := by
    rw [heq1] at hd1
    exact_mod_cast (show p ∣ s m * R1 + sigma m by simpa [Nat.mul_comm] using hd1)
  have hdiv2 : (p : ℤ) ∣ (s m : ℤ) * R2 + sigma m := by
    rw [heq2] at hd2
    exact_mod_cast (show p ∣ s m * R2 + sigma m by simpa [Nat.mul_comm] using hd2)
  have hh := AmicableAudit.linearResidueUnique p (s m) (sigma m) R1 R2
    (by exact_mod_cast hp.pos) hc hdiv1 hdiv2 (by positivity) (by positivity)
    (by exact_mod_cast hsmall1) (by exact_mod_cast hsmall2)
  exact_mod_cast hh

theorem reconstructionPowerGap {u v : ℝ} (hu : u ≤ 1) (hgap : 2 * u < v) :
    ∀ᶠ x : ℝ in atTop, ∀ m V R1 R2 : ℕ,
      0 < R1 → 0 < R2 → (R1 : ℝ) ≤ x ^ u → (R2 : ℝ) ≤ x ^ u →
      x ^ v ≤ (V : ℝ) →
      m.Coprime R1 → m.Coprime R2 →
      R1.Coprime (s (m * R1)) → R2.Coprime (s (m * R2)) →
      V.Coprime (m * R1) → V ∣ s (m * R1) → V ∣ s (m * R2) → R1 = R2 := by
  let e := (v - 2 * u) / 4
  have he : 0 < e := by dsimp [e]; linarith
  filter_upwards [AmicableSigmaBounds.determinantUniform he,
    eventually_gt_atTop (Real.exp 1)] with x hx hxexp
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hxexp
  have hx0 : 0 < x := by linarith
  have hlog : 1 < Real.log x := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hxexp
  intro m V R1 R2 hR1 hR2 hb1 hb2 hV hm1 hm2 hc1 hc2 hVm hd1 hd2
  have hU : x ^ u ≤ x * Real.log x := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1.le hu
    rw [Real.rpow_one] at hh
    nlinarith
  have hdet := hx R1 R2 (x ^ u) (Real.rpow_pos_of_pos hx0 _) hb1 hb2 hU
  have hid : (x ^ u) ^ 2 * x ^ (2 * e) = x ^ (2 * u + 2 * e) := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  rw [hid] at hdet
  have hexp : 2 * u + 2 * e < v := by dsimp [e]; linarith
  have hsize := hdet.trans_le ((Real.rpow_lt_rpow_of_exponent_lt hx1 hexp).le.trans hV)
  have hVpos : 0 < V := by
    have hh := (Real.rpow_pos_of_pos hx0 v).trans_le hV
    exact_mod_cast hh
  apply divisorSumReconstruction hVpos hR1 hR2 hm1 hm2 hc1 hc2 hVm hd1 hd2
  exact_mod_cast hsize

#print axioms primeReconstruction
#print axioms reconstructionPowerGap
end AmicableCases

