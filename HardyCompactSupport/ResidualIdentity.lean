import Std
import HardyCompactSupport.ConstructionStatement
import HardyCompactSupport.WidthEquation
import HardyCompactSupport.PhaseEquation

/-!
# PDE residual algebra

This file contains small algebraic cancellations used by the residual
computation before the full analytic definitions of `u` and `V` are introduced.
-/

namespace HardyCompactSupport
namespace ResidualIdentity

/-- NODE HE.ResidualIdentity.quadratic_cancel
deps: HE.WidthEquation.y_ode
statement: `y''=16/y^3` cancels the quadratic coefficient after clearing denominators.
-/
theorem quadratic_cancel (y ydd : Int) (h : ydd * y^3 = 16) :
    - ydd * y^3 + 16 = 0 := by
  grind

/-- NODE HE.ResidualIdentity.even_residual
deps: HE.AlgebraicIdentities.RN.tail_degree, HE.WidthEquation.y_ode, HE.PhaseEquation.continuity, HE.ResidualIdentity.quadratic_cancel
statement: even profile satisfies `i∂_t u + Δu = V_N u`.
-/
theorem even_residual : ConstructionStatement.EvenResidualClaim := by
  exact
    { width_ode := by
        intro q qp qpp y yp ypp hq hqp hqpp hdisc hy
        exact WidthEquation.width_y_ode q qp qpp y yp ypp hq hqp hqpp hdisc hy
      phase_continuity := by
        intro n b y yp h
        exact PhaseEquation.phase_continuity n b y yp h
      quadratic_cancel := by
        intro y ydd h
        exact quadratic_cancel y ydd h
      rational_tail_linear := by
        intro n k
        exact AlgebraicIdentities.RN_tail_degree n k }

/-- NODE HE.ResidualIdentity.odd_residual
deps: HE.AlgebraicIdentities.RD.tail_degree, HE.WidthEquation.y_ode, HE.PhaseEquation.continuity, HE.ResidualIdentity.quadratic_cancel
statement: odd profile satisfies `i∂_t u + Δu = V_D u`.
-/
theorem odd_residual : ConstructionStatement.OddResidualClaim := by
  exact
    { width_ode := by
        intro q qp qpp y yp ypp hq hqp hqpp hdisc hy
        exact WidthEquation.width_y_ode q qp qpp y yp ypp hq hqp hqpp hdisc hy
      phase_continuity := by
        intro n b y yp h
        exact PhaseEquation.phase_continuity n b y yp h
      quadratic_cancel := by
        intro y ydd h
        exact quadratic_cancel y ydd h
      rational_tail_linear := by
        intro n k
        exact AlgebraicIdentities.RD_tail_degree n k }

end ResidualIdentity
end HardyCompactSupport



