import Std
import HardyCompactSupport.ConstructionStatement
import HardyCompactSupport.DecayEstimates

/-!
# Final theorem node
-/

namespace HardyCompactSupport
namespace IntermediateResults

/-- NODE HE.IntermediateResults.real_scalar_endpoint
deps: HE.ResidualIdentity.even_residual, HE.ResidualIdentity.odd_residual, HE.DecayEstimates.endpoint_L2
statement: existence of a bounded real scalar Hardy endpoint example.
-/
theorem real_scalar_endpoint : ConstructionStatement.RealScalarEndpointClaim := by
  have hparams : ConstructionStatement.SimpleEndpointParameters := by
    refine ⟨1, 2, 2, 1, 1, ?_⟩
    norm_num
  exact
    { parameters := hparams
      nonzero_solution := DecayEstimates.endpoint_L2.nonzero_solution
      bounded_real_scalar_potential := DecayEstimates.endpoint_L2.bounded_real_scalar_potential
      even_residual := ResidualIdentity.even_residual
      odd_residual := ResidualIdentity.odd_residual
      endpoint_weighted_L2 := DecayEstimates.endpoint_L2.endpoint_weighted_L2 }

end IntermediateResults
end HardyCompactSupport



