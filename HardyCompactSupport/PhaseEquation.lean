import Std
import HardyCompactSupport.WidthEquation

/-!
# Phase transport algebra

These are denominator-free algebraic fragments of the continuity-equation
calculation.  The analytic version will later instantiate
`4 b y = y'`.
-/

namespace HardyCompactSupport
namespace PhaseEquation

/-- NODE HE.PhaseEquation.transport_xi_coeff
deps:
statement: `4b=y'/y` makes the profile-transport coefficient vanish.
-/
theorem transport_xi_coeff (b y yp : Int) (h : 4 * b * y = yp) :
    4 * b * y - yp = 0 := by
  grind

/-- NODE HE.PhaseEquation.transport_mass_coeff
deps: HE.PhaseEquation.transport_xi_coeff
statement: the mass coefficient also vanishes after multiplying by the common denominator.
-/
theorem transport_mass_coeff (n b y yp : Int) (h : 4 * b * y = yp) :
    4 * b * n * y - n * yp = 0 := by
  grind

/-- NODE HE.PhaseEquation.continuity
deps: HE.PhaseEquation.transport_xi_coeff, HE.PhaseEquation.transport_mass_coeff
statement: `b=y'/(4y)` makes the imaginary part vanish.
-/
theorem phase_continuity (n b y yp : Int) (h : 4 * b * y = yp) :
    (4 * b * y - yp = 0) ∧ (4 * b * n * y - n * yp = 0) := by
  exact ⟨transport_xi_coeff b y yp h, transport_mass_coeff n b y yp h⟩

end PhaseEquation
end HardyCompactSupport



