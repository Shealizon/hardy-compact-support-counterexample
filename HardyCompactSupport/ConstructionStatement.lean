import Mathlib
import HardyCompactSupport.AlgebraicIdentities
import HardyCompactSupport.WidthEquation
import HardyCompactSupport.PhaseEquation
import HardyCompactSupport.TimeScaling

/-!
# Claim interface for the endpoint theorem

This file records the theorem-level interface we ultimately want to prove.
The atomic claims below are deliberately abstract for now: later files should
replace these interfaces by concrete definitions of the solution, potential,
PDE residuals, and weighted endpoint integrals.
-/

noncomputable section

namespace HardyCompactSupport
namespace ConstructionStatement

/--
The normalized endpoint parameter regime used as the first concrete target:
spatial dimension `n = 1`, endpoint widths `A = B = 2`, time horizon `T = 1`,
and decay exponent above the integrability threshold `(n+2)/4`.
-/
def SimpleEndpointParameters : Prop :=
  ∃ n : Nat, ∃ A B T k : ℝ,
    n = 1 ∧ A = 2 ∧ B = 2 ∧ T = 1 ∧
      A * B = 4 * T ∧ ((n : ℝ) + 2) / 4 < k

/--
Non-vanishing data for the simple endpoint profile.  This is the current
formal proxy for the eventual statement that the constructed solution is not
identically zero.
-/
structure NonzeroSolutionClaim : Prop where
  width_positive : ∀ t : ℝ, 0 < TimeScaling.ySym t
  width_nonzero : ∀ t : ℝ, TimeScaling.ySym t ≠ 0

/--
Bounded-potential data available at the algebraic layer: the even and odd
rational tails reduce to linear numerators after the endpoint cancellation,
and the simple width satisfies the endpoint ODE.
-/
structure BoundedRealScalarPotentialClaim : Prop where
  even_tail_linear :
    ∀ n k : Int,
      AlgebraicIdentities.IsLinearInt (fun z => AlgebraicIdentities.RNRawNum n k z - AlgebraicIdentities.RNInfNum k z)
  odd_tail_linear :
    ∀ n k : Int,
      AlgebraicIdentities.IsLinearInt
        (fun z => AlgebraicIdentities.RNRawNum n k z - AlgebraicIdentities.RNInfNum k z -
          AlgebraicIdentities.RDExtraNum k z)
  endpoint_width_ode :
    ∀ t : ℝ, deriv (deriv TimeScaling.ySym) t = 16 / (TimeScaling.ySym t)^3

/--
Endpoint weighted `L^2` data currently formalized for the normalized
`A = B = 2`, `T = 1` case.
-/
structure EndpointWeightedL2Claim : Prop where
  parameters : SimpleEndpointParameters
  threshold_example : ((1 : ℝ) + 2) / 4 < 1
  width_positive : ∀ t : ℝ, 0 < TimeScaling.ySym t
  endpoint_width_ode :
    ∀ t : ℝ, deriv (deriv TimeScaling.ySym) t = 16 / (TimeScaling.ySym t)^3

/--
Algebraic residual package for the even reflected profile.  The current layer
does not yet define the full analytic solution `u` and potential `V`; instead
it records the cancellations that the eventual residual computation must use.
-/
structure EvenResidualClaim : Prop where
  width_ode :
    ∀ (q qp qpp y yp ypp : ℝ),
      q = y^2 →
      qp = 2 * y * yp →
      qpp = 2 * yp^2 + 2 * y * ypp →
      2 * qpp * q - qp^2 = 64 →
      y^3 ≠ 0 →
      ypp = 16 / y^3
  phase_continuity :
    ∀ n b y yp : Int,
      4 * b * y = yp →
        (4 * b * y - yp = 0) ∧ (4 * b * n * y - n * yp = 0)
  quadratic_cancel :
    ∀ y ydd : Int, ydd * y^3 = 16 → - ydd * y^3 + 16 = 0
  rational_tail_linear :
    ∀ n k : Int,
      AlgebraicIdentities.IsLinearInt (fun z => AlgebraicIdentities.RNRawNum n k z - AlgebraicIdentities.RNInfNum k z)

/--
Algebraic residual package for the odd reflected profile.  It shares the
width, phase, and quadratic cancellations with the even profile, but uses the
odd rational-tail identity.
-/
structure OddResidualClaim : Prop where
  width_ode :
    ∀ (q qp qpp y yp ypp : ℝ),
      q = y^2 →
      qp = 2 * y * yp →
      qpp = 2 * yp^2 + 2 * y * ypp →
      2 * qpp * q - qp^2 = 64 →
      y^3 ≠ 0 →
      ypp = 16 / y^3
  phase_continuity :
    ∀ n b y yp : Int,
      4 * b * y = yp →
        (4 * b * y - yp = 0) ∧ (4 * b * n * y - n * yp = 0)
  quadratic_cancel :
    ∀ y ydd : Int, ydd * y^3 = 16 → - ydd * y^3 + 16 = 0
  rational_tail_linear :
    ∀ n k : Int,
      AlgebraicIdentities.IsLinearInt
        (fun z => AlgebraicIdentities.RNRawNum n k z - AlgebraicIdentities.RNInfNum k z -
          AlgebraicIdentities.RDExtraNum k z)

/--
Analytic package supplied by the decay/boundedness layer.  This is intentionally
stronger than the short label `endpoint_L2`: it records the extra facts that the
final theorem needs from the analytic part of the construction.
-/
structure EndpointL2Claim : Prop where
  nonzero_solution : NonzeroSolutionClaim
  bounded_real_scalar_potential : BoundedRealScalarPotentialClaim
  endpoint_weighted_L2 : EndpointWeightedL2Claim

/-- The final theorem-level claim for the normalized endpoint example. -/
structure RealScalarEndpointClaim : Prop where
  parameters : SimpleEndpointParameters
  nonzero_solution : NonzeroSolutionClaim
  bounded_real_scalar_potential : BoundedRealScalarPotentialClaim
  even_residual : EvenResidualClaim
  odd_residual : OddResidualClaim
  endpoint_weighted_L2 : EndpointWeightedL2Claim

end ConstructionStatement
end HardyCompactSupport



