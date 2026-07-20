import HardyCompactSupport.EndpointDecayAndSupport

/-!
# Final endpoint properties

This module converts the construction's exterior vanishing estimate into the
intrinsic statement that each time slice of the potential has compact
topological support.  The radius used in the proof is deliberately absent from
the public theorem.
-/

noncomputable section

namespace HardyCompactSupport
namespace EndpointVerification

open CompactSupportConstruction

/-- Every time slice of the constructed potential has compact support in `ℝ`. -/
theorem constructedPotential_has_compact_support :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsCompact (tsupport (compactPotential compactProfileData t)) := by
  intro t ht
  let radiusAtTime := compactProfileData.radius * TimeScaling.ySym t
  have support_subset :
      Function.support (compactPotential compactProfileData t) ⊆
        Set.Icc (-radiusAtTime) radiusAtTime := by
    intro x hx
    have habs : |x| ≤ radiusAtTime := by
      apply le_of_not_gt
      intro houtside
      exact hx (compactCandidate_compact_support t ht x houtside)
    exact (abs_le.mp habs)
  have topologicalSupport_subset :
      tsupport (compactPotential compactProfileData t) ⊆
        Set.Icc (-radiusAtTime) radiusAtTime := by
    exact closure_minimal support_subset isClosed_Icc
  exact isCompact_Icc.of_isClosed_subset isClosed_closure topologicalSupport_subset

end EndpointVerification
end HardyCompactSupport
