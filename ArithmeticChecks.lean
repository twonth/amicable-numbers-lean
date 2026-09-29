import Std

/-! Exact rational checks on constants. These are not asymptotic estimates. -/
namespace AmicableAudit

theorem caseOneSlack : (1 : Rat) - (4 / 5) * (10 / 9) > 1 / 10 := by
  grind

theorem caseTwoSavingIdentity (e : Rat) :
    (1 / 2 - e) * (2 * e + 4 * e ^ 2) = e - 4 * e ^ 3 := by
  grind

theorem averagingGapIdentity (e : Rat) :
    (1 / 2 - e) * (1 - 2 * e - 3 * e ^ 2) -
      (1 / 2 - 3 * e + e ^ 2) = e * (1 - e / 2 + 3 * e ^ 2) := by
  grind

theorem reconstructionExponentGap (e : Rat) :
    (2 * e + 3 * e ^ 2) - (2 * e + 2 * e ^ 2) = e ^ 2 := by
  grind

theorem caseOneReconstructionGap (e : Rat) :
    e ^ 2 - 4 * (e ^ 2 / 10) = (3 / 5) * e ^ 2 := by
  grind

theorem averagingGapPositive (e : Rat) (he : 0 < e) (hu : e < 1 / 10) :
    (1 / 2 - e) * (1 - 2 * e - 3 * e ^ 2) >
      1 / 2 - 3 * e + e ^ 2 := by
  have hsq : 0 < e ^ 2 := by
    have := Rat.mul_pos he he
    grind
  have hfactor : 0 < 1 - e / 2 + 3 * e ^ 2 := by grind
  have hprod := Rat.mul_pos he hfactor
  have hid := averagingGapIdentity e
  grind

theorem caseTwoSavingPositive (e : Rat) (he : 0 < e) : 0 < 4 * e ^ 3 := by
  have hs := Rat.mul_pos he he
  have hc := Rat.mul_pos he hs
  grind

#print axioms caseOneSlack
#print axioms caseTwoSavingIdentity
#print axioms averagingGapIdentity
#print axioms reconstructionExponentGap
#print axioms caseOneReconstructionGap
#print axioms averagingGapPositive
#print axioms caseTwoSavingPositive

end AmicableAudit
