import Mathlib
import HardyCompactSupport.AlgebraicIdentities

/-!
# Width identities

This layer formalizes the polynomial part of the endpoint width computation.
The analytic statement `y'' = 16 / y^3` will be connected later; here we prove
the discriminant identity for the quadratic numerator.
-/

namespace HardyCompactSupport
namespace WidthEquation

/--
Numerator for `T^2 y(t)^2`:
`Q(t)=B^2 (T-t)^2 + A^2 t^2`.
-/
def Qnum (A B T t : Int) : Int :=
  B^2 * (T - t)^2 + A^2 * t^2

/-- Formal derivative of `Qnum` with respect to `t`. -/
def QnumDeriv (A B T t : Int) : Int :=
  2 * (A^2 + B^2) * t - 2 * B^2 * T

/-- Formal second derivative of `Qnum` with respect to `t`. -/
def QnumSecond (A B : Int) : Int :=
  2 * (A^2 + B^2)

/-- NODE HE.WidthEquation.q_identity
deps:
statement: discriminant identity for `Q(t)=B^2(T-t)^2+A^2t^2`.
-/
theorem q_identity (A B T t : Int) :
    2 * QnumSecond A B * Qnum A B T t - (QnumDeriv A B T t)^2 =
      4 * A^2 * B^2 * T^2 := by
  unfold Qnum QnumDeriv QnumSecond
  grind

/-- NODE HE.WidthEquation.endpoint_q_identity
deps: HE.WidthEquation.q_identity
statement: under `AB=4T`, the quadratic identity has endpoint constant `64T^4`.
-/
theorem endpoint_q_identity (A B T t : Int) (h : A * B = 4 * T) :
    2 * QnumSecond A B * Qnum A B T t - (QnumDeriv A B T t)^2 =
      64 * T^4 := by
  rw [q_identity]
  grind

/-!
The next lemma is the algebraic core of the passage from a quadratic identity
for `q = y^2` to the ODE for `y`.  The real-analysis layer must later prove the
three differential relations for the actual function `y = sqrt q`.
-/

/-- NODE HE.WidthEquation.sqrt_chain_to_ode
deps:
statement: from `q=y^2` and the differentiated square identities, the endpoint discriminant gives `y^3 y''=16`.
-/
theorem sqrt_chain_to_ode
    (q qp qpp y yp ypp : Int)
    (hq : q = y^2)
    (hqp : qp = 2 * y * yp)
    (hqpp : qpp = 2 * yp^2 + 2 * y * ypp)
    (hdisc : 2 * qpp * q - qp^2 = 64) :
    y^3 * ypp = 16 := by
  subst q
  subst qp
  subst qpp
  grind

/-- NODE HE.WidthEquation.sqrt_chain_to_ode_real
deps:
statement: real version of the algebraic passage from `q=y^2` and the endpoint discriminant to `y^3 y''=16`.
-/
theorem sqrt_chain_to_ode_real
    (q qp qpp y yp ypp : ℝ)
    (hq : q = y^2)
    (hqp : qp = 2 * y * yp)
    (hqpp : qpp = 2 * yp^2 + 2 * y * ypp)
    (hdisc : 2 * qpp * q - qp^2 = 64) :
    y^3 * ypp = 16 := by
  subst q
  subst qp
  subst qpp
  ring_nf at hdisc ⊢
  nlinarith

/-- NODE HE.WidthEquation.symmetric_q_identity
deps: HE.WidthEquation.q_identity
statement: in the simple endpoint case `A=B=2,T=1`, the quadratic discriminant is `64`.
-/
theorem symmetric_q_identity (t : Int) :
    2 * QnumSecond 2 2 * Qnum 2 2 1 t - (QnumDeriv 2 2 1 t)^2 = 64 := by
  rw [q_identity]
  grind

/-- NODE HE.WidthEquation.symmetric_y_ode_formal
deps: HE.WidthEquation.symmetric_q_identity, HE.WidthEquation.sqrt_chain_to_ode
statement: formal ODE core for the simple case `A=B=2,T=1`: `y^3 y'' = 16`.
-/
theorem symmetric_y_ode_formal
    (t q qp qpp y yp ypp : Int)
    (hQ : q = Qnum 2 2 1 t)
    (hQp : qp = QnumDeriv 2 2 1 t)
    (hQpp : qpp = QnumSecond 2 2)
    (hq : q = y^2)
    (hqp : qp = 2 * y * yp)
    (hqpp : qpp = 2 * yp^2 + 2 * y * ypp) :
    y^3 * ypp = 16 := by
  apply sqrt_chain_to_ode q qp qpp y yp ypp hq hqp hqpp
  subst q
  subst qp
  subst qpp
  exact symmetric_q_identity t

/-- NODE HE.WidthEquation.y_ode
deps: HE.WidthEquation.sqrt_chain_to_ode_real
statement: `y'' = 16 / y^3` from the real endpoint width chain identities.
-/
theorem width_y_ode
    (q qp qpp y yp ypp : ℝ)
    (hq : q = y^2)
    (hqp : qp = 2 * y * yp)
    (hqpp : qpp = 2 * yp^2 + 2 * y * ypp)
    (hdisc : 2 * qpp * q - qp^2 = 64)
    (hy : y^3 ≠ 0) :
    ypp = 16 / y^3 := by
  have hmul : y^3 * ypp = 16 :=
    sqrt_chain_to_ode_real q qp qpp y yp ypp hq hqp hqpp hdisc
  have hdiv : (y^3 * ypp) / y^3 = 16 / y^3 := by
    rw [hmul]
  have hleft : (y^3 * ypp) / y^3 = ypp := by
    exact mul_div_cancel_left₀ ypp hy
  rw [hleft] at hdiv
  exact hdiv

end WidthEquation
end HardyCompactSupport



