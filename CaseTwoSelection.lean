import ManuscriptArithmetic
import RankinParameters

namespace AmicableCases
open AmicableManuscript
open scoped BigOperators

noncomputable def selectionGap (e : ℝ) : ℝ :=
  (1 / 2 - e) * (1 - 2 * e - 3 * e ^ 2) - (1 / 2 - 3 * e + e ^ 2)

theorem selectionGap_pos {e : ℝ} (he : 0 < e) (he1 : e < 1 / 10) : 0 < selectionGap e :=
  sub_pos.mpr (averagingGapPositive e he he1)

/-- The averaging argument, including the discarded term indexed by zero. -/
theorem caseTwoSelectIndex {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (cost weight : ι → ℝ) (cost0 e E delta : ℝ)
    (he : 0 < e) (he1 : e < 1 / 10) (hE : 0 < E)
    (hd0 : 0 ≤ delta) (hd : delta ≤ selectionGap e / 4)
    (hzero : -delta * E ≤ cost0)
    (hcost : cost0 + ∑ i ∈ I, cost i ≤ (1 / 2 - 3 * e + e ^ 2 + delta) * E)
    (hweight : (1 - 2 * e - 3 * e ^ 2 - delta) * E ≤ ∑ i ∈ I, weight i) :
    ∃ i ∈ I, cost i ≤ (1 / 2 - e) * weight i := by
  apply weightedSelection I hI cost weight (1 / 2 - e)
  have hc : 0 < 1 / 2 - e := by linarith
  have hupper : ∑ i ∈ I, cost i ≤ (1 / 2 - 3 * e + e ^ 2 + 2 * delta) * E := by
    nlinarith
  have hlower := mul_le_mul_of_nonneg_left hweight hc.le
  have hgap := selectionGap_pos he he1
  have hcoef : 1 / 2 - 3 * e + e ^ 2 + 2 * delta ≤
      (1 / 2 - e) * (1 - 2 * e - 3 * e ^ 2 - delta) := by
    dsimp [selectionGap] at hd hgap
    nlinarith
  have hmid := mul_le_mul_of_nonneg_right hcoef hE.le
  nlinarith

theorem caseTwoBudgetFromLog {x e : ℝ} {V d : ℕ}
    (hx : 1 < x) (he : 0 < e) (he1 : e < 1 / 10) (hV : 1 < V) (hd : 0 < d)
    (hVupper : (V : ℝ) ≤ x ^ (2 * e + 4 * e ^ 2))
    (hcost : Real.log ((V : ℝ) / d) + Real.log (Real.log x) * (ArithmeticFunction.cardFactors d : ℝ) ≤
      (1 / 2 - e) * Real.log (V : ℝ)) :
    1 < d ∧ ((V : ℝ) / d) *
      Real.exp ((ArithmeticFunction.cardFactors d : ℝ) * Real.log (Real.log x)) ≤ x ^ (e - 4 * e ^ 3) := by
  have hVpos : (0 : ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hx0 : 0 < x := by linarith
  have hc : 0 < 1 / 2 - e := by linarith
  constructor
  · by_contra hh
    have hd1 : d = 1 := by omega
    rw [hd1] at hcost
    simp only [Nat.cast_one, div_one, ArithmeticFunction.cardFactors_one, Nat.cast_zero, mul_zero, add_zero] at hcost
    have hlV : 0 < Real.log (V : ℝ) := Real.log_pos (by exact_mod_cast hV)
    nlinarith
  · have hlogV := Real.log_le_log hVpos hVupper
    rw [Real.log_rpow hx0] at hlogV
    have hmult := mul_le_mul_of_nonneg_left hlogV hc.le
    have hbound : Real.log ((V : ℝ) / d) +
        (ArithmeticFunction.cardFactors d : ℝ) * Real.log (Real.log x) ≤
        Real.log x * (e - 4 * e ^ 3) := by
      have hid := caseTwoSavingIdentity e
      nlinarith
    have hh := Real.exp_le_exp.mpr hbound
    rw [Real.exp_add, Real.exp_log (div_pos hVpos hdpos), ← Real.rpow_def_of_pos hx0] at hh
    exact hh

#print axioms selectionGap_pos
#print axioms caseTwoSelectIndex
#print axioms caseTwoBudgetFromLog
end AmicableCases
