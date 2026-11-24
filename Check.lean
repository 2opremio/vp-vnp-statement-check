import Bridge

-- The bridge theorems have exactly the types of the independent claims.
example : Independent.MainLowerBound.{0} := Bridge.bridge_main
example : Independent.MainLowerBoundBorder.{0} := Bridge.bridge_border
example : Independent.VP_ssubset_VNP.{0} := Bridge.bridge_sep
example : Independent.VNP_not_subset_VPbar.{0} := Bridge.bridge_closure
example : Independent.PermanentRealLowerBound := Bridge.bridge_real

#print axioms Bridge.bridge_main
#print axioms Bridge.bridge_border
#print axioms Bridge.bridge_sep
#print axioms Bridge.bridge_closure
#print axioms Bridge.bridge_real
