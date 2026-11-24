import Independent

/-! The five claims of `Independent.lean`, with `sorry` in place of the proofs, for the tool
Comparator. This file imports `Independent` alone, and that file imports Mathlib alone. Nothing
imports this file. -/

namespace Bridge

universe u

theorem bridge_main : Independent.MainLowerBound.{u} := by
  sorry

theorem bridge_border : Independent.MainLowerBoundBorder.{u} := by
  sorry

theorem bridge_sep : Independent.VP_ssubset_VNP.{u} := by
  sorry

theorem bridge_closure : Independent.VNP_not_subset_VPbar.{u} := by
  sorry

theorem bridge_real : Independent.PermanentRealLowerBound := by
  sorry

end Bridge
