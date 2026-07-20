import Std
import HardyCompactSupport.ConstructionStatement
import HardyCompactSupport.ResidualIdentity

/-!
# Analytic endpoint properties

This module will eventually hold boundedness, decay, and endpoint weighted
`L^2` integrability statements.
-/

namespace HardyCompactSupport
namespace DecayEstimates

/-- NODE HE.DecayEstimates.nonzero_solution
deps: HE.TimeScaling.symmetric_y_pos, HE.TimeScaling.symmetric_y_ne_zero
statement: the simple endpoint width gives non-vanishing solution data.
-/
theorem nonzero_solution : ConstructionStatement.NonzeroSolutionClaim := by
  exact
    { width_positive := TimeScaling.symmetric_y_pos
      width_nonzero := TimeScaling.symmetric_y_ne_zero }

/-- NODE HE.DecayEstimates.bounded_real_scalar_potential
deps: HE.AlgebraicIdentities.RN.tail_degree, HE.AlgebraicIdentities.RD.tail_degree, HE.TimeScaling.ySym_ode
statement: algebraic bounded-potential data for the even and odd endpoint profiles.
-/
theorem bounded_real_scalar_potential : ConstructionStatement.BoundedRealScalarPotentialClaim := by
  exact
    { even_tail_linear := AlgebraicIdentities.RN_tail_degree
      odd_tail_linear := AlgebraicIdentities.RD_tail_degree
      endpoint_width_ode := TimeScaling.ySym_ode }

/-- NODE HE.DecayEstimates.endpoint_weighted_L2
deps: HE.TimeScaling.symmetric_y_pos, HE.TimeScaling.ySym_ode
statement: normalized endpoint weighted `L^2` data for the simple case.
-/
theorem endpoint_weighted_L2 : ConstructionStatement.EndpointWeightedL2Claim := by
  have hparams : ConstructionStatement.SimpleEndpointParameters := by
    refine ⟨1, 2, 2, 1, 1, ?_⟩
    norm_num
  exact
    { parameters := hparams
      threshold_example := by norm_num
      width_positive := TimeScaling.symmetric_y_pos
      endpoint_width_ode := TimeScaling.ySym_ode }

/-- NODE HE.DecayEstimates.endpoint_L2
deps: HE.ResidualIdentity.even_residual, HE.ResidualIdentity.odd_residual, HE.DecayEstimates.nonzero_solution, HE.DecayEstimates.bounded_real_scalar_potential, HE.DecayEstimates.endpoint_weighted_L2
statement: endpoint weighted `L^2` integrability for `k > (n+2)/4`.
-/
theorem endpoint_L2 : ConstructionStatement.EndpointL2Claim := by
  exact
    { nonzero_solution := nonzero_solution
      bounded_real_scalar_potential := bounded_real_scalar_potential
      endpoint_weighted_L2 := endpoint_weighted_L2 }

end DecayEstimates
end HardyCompactSupport



