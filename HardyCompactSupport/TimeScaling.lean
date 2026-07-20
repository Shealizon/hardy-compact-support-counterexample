import Mathlib
import HardyCompactSupport.WidthEquation

/-!
# Real width layer

This module begins the Mathlib-backed real-analysis layer.  It first handles
the simple endpoint case `A = B = 2`, `T = 1`, where

`q(t) = (1 - t)^2 + t^2`.

The next analytic target is to connect these facts to the derivative identities
needed by `HE.WidthEquation.y_ode`.
-/

noncomputable section

namespace HardyCompactSupport
namespace TimeScaling

def qSym (t : ℝ) : ℝ :=
  (1 - t)^2 + t^2

def ySym (t : ℝ) : ℝ :=
  2 * Real.sqrt (qSym t)

def ySymPrime : ℝ → ℝ :=
  (fun t : ℝ => 4 * t - 2) / fun t => Real.sqrt (qSym t)

/-- NODE HE.TimeScaling.symmetric_q_pos
deps:
statement: in the simple case, `q(t)=(1-t)^2+t^2` is strictly positive.
-/
theorem symmetric_q_pos (t : ℝ) : 0 < qSym t := by
  unfold qSym
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]

/-- NODE HE.TimeScaling.symmetric_q_ne_zero
deps: HE.TimeScaling.symmetric_q_pos
statement: the simple-case quadratic never vanishes, enabling the sqrt derivative rule.
-/
theorem symmetric_q_ne_zero (t : ℝ) : qSym t ≠ 0 := by
  exact ne_of_gt (symmetric_q_pos t)

/-- NODE HE.TimeScaling.symmetric_sqrt_sq
deps: HE.TimeScaling.symmetric_q_pos
statement: `(sqrt q)^2=q` for the simple positive quadratic.
-/
theorem symmetric_sqrt_sq (t : ℝ) : (Real.sqrt (qSym t))^2 = qSym t := by
  rw [Real.sq_sqrt]
  exact le_of_lt (symmetric_q_pos t)

/-- NODE HE.TimeScaling.symmetric_y_sq
deps: HE.TimeScaling.symmetric_sqrt_sq
statement: `y(t)=2 sqrt(q(t))` satisfies `y(t)^2=4q(t)`.
-/
theorem symmetric_y_sq (t : ℝ) : (ySym t)^2 = 4 * qSym t := by
  unfold ySym
  rw [mul_pow, symmetric_sqrt_sq]
  norm_num

/-- NODE HE.TimeScaling.qSym_deriv
deps:
statement: first derivative of the simple quadratic is `4t-2`.
-/
theorem qSym_deriv (t : ℝ) : deriv qSym t = 4 * t - 2 := by
  unfold qSym
  change deriv (((fun t : ℝ => 1 - t)^2) + ((fun t : ℝ => t)^2)) t = 4 * t - 2
  rw [deriv_add]
  · rw [deriv_pow]
    · rw [deriv_pow]
      · simp
        ring
      · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

/-- NODE HE.TimeScaling.qSym_hasDerivAt
deps: HE.TimeScaling.qSym_deriv
statement: the simple quadratic has derivative `4t-2` in the `HasDerivAt` form.
-/
theorem qSym_hasDerivAt (t : ℝ) : HasDerivAt qSym (4 * t - 2) t := by
  have hd : DifferentiableAt ℝ qSym t := by
    unfold qSym
    fun_prop
  simpa [qSym_deriv t] using hd.hasDerivAt

theorem qSym_deriv_fun : deriv qSym = fun t => 4 * t - 2 := by
  funext t
  exact qSym_deriv t

/-- NODE HE.TimeScaling.qSym_second_deriv
deps: HE.TimeScaling.qSym_deriv
statement: second derivative of the simple quadratic is `4`.
-/
theorem qSym_second_deriv (t : ℝ) : deriv (deriv qSym) t = 4 := by
  rw [qSym_deriv_fun]
  change deriv (((fun t : ℝ => 4) * (fun t : ℝ => t)) - (fun _ : ℝ => 2)) t = 4
  rw [deriv_sub]
  · rw [deriv_mul]
    · simp
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

/-- NODE HE.TimeScaling.symmetric_y_pos
deps: HE.TimeScaling.symmetric_q_pos
statement: the simple-case width `y(t)=2 sqrt(q(t))` is strictly positive.
-/
theorem symmetric_y_pos (t : ℝ) : 0 < ySym t := by
  unfold ySym
  have hsqrt : 0 < Real.sqrt (qSym t) := Real.sqrt_pos.2 (symmetric_q_pos t)
  positivity

/-- NODE HE.TimeScaling.symmetric_y_ne_zero
deps: HE.TimeScaling.symmetric_y_pos
statement: the simple-case width never vanishes.
-/
theorem symmetric_y_ne_zero (t : ℝ) : ySym t ≠ 0 := by
  exact ne_of_gt (symmetric_y_pos t)

/-- NODE HE.TimeScaling.symmetric_y_cube_ne_zero
deps: HE.TimeScaling.symmetric_y_ne_zero
statement: the cube of the simple-case width never vanishes.
-/
theorem symmetric_y_cube_ne_zero (t : ℝ) : (ySym t)^3 ≠ 0 := by
  exact pow_ne_zero 3 (symmetric_y_ne_zero t)

/-- NODE HE.TimeScaling.sqrt_qSym_hasDerivAt
deps: HE.TimeScaling.qSym_hasDerivAt, HE.TimeScaling.symmetric_q_ne_zero
statement: derivative of `sqrt(q(t))` in the simple endpoint case.
-/
theorem sqrt_qSym_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.sqrt (qSym s))
      ((4 * t - 2) / (2 * Real.sqrt (qSym t))) t := by
  exact (qSym_hasDerivAt t).sqrt (symmetric_q_ne_zero t)

/-- NODE HE.TimeScaling.ySym_hasDerivAt
deps: HE.TimeScaling.sqrt_qSym_hasDerivAt, HE.TimeScaling.symmetric_q_pos
statement: first derivative of `y(t)=2 sqrt(q(t))` in the simple endpoint case.
-/
theorem ySym_hasDerivAt (t : ℝ) :
    HasDerivAt ySym ((4 * t - 2) / Real.sqrt (qSym t)) t := by
  unfold ySym
  have hmul := (sqrt_qSym_hasDerivAt t).const_mul 2
  have hsqrt_ne : Real.sqrt (qSym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (symmetric_q_pos t))
  have hcoef : 2 * ((4 * t - 2) / (2 * Real.sqrt (qSym t))) =
      (4 * t - 2) / Real.sqrt (qSym t) := by
    field_simp [hsqrt_ne]
  simpa [hcoef] using hmul

/-- NODE HE.TimeScaling.ySymPrime_hasDerivAt
deps: HE.TimeScaling.sqrt_qSym_hasDerivAt, HE.TimeScaling.symmetric_sqrt_sq
statement: derivative of the explicit first-derivative formula for `y(t)`.
-/
theorem ySymPrime_hasDerivAt (t : ℝ) :
    HasDerivAt ySymPrime (2 / (Real.sqrt (qSym t))^3) t := by
  unfold ySymPrime
  have hnum : HasDerivAt (fun s : ℝ => 4 * s - 2) 4 t := by
    have hd : DifferentiableAt ℝ (fun s : ℝ => 4 * s - 2) t := by
      fun_prop
    have hderiv : deriv (fun s : ℝ => 4 * s - 2) t = 4 := by
      simp
    simpa [hderiv] using hd.hasDerivAt
  have hsqrt := sqrt_qSym_hasDerivAt t
  have hsqrt_ne : Real.sqrt (qSym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (symmetric_q_pos t))
  have hdiv := hnum.div hsqrt hsqrt_ne
  have hcoef :
      (4 * Real.sqrt (qSym t) -
            (4 * t - 2) * ((4 * t - 2) / (2 * Real.sqrt (qSym t)))) /
          Real.sqrt (qSym t)^2 =
        2 / Real.sqrt (qSym t)^3 := by
    have hsq : (Real.sqrt (qSym t))^2 = qSym t := symmetric_sqrt_sq t
    field_simp [hsqrt_ne]
    rw [hsq]
    unfold qSym
    ring
  simpa [hcoef] using hdiv

/-- NODE HE.TimeScaling.ySym_deriv_fun
deps: HE.TimeScaling.ySym_hasDerivAt
statement: the derivative function of `ySym` is the explicit formula `ySymPrime`.
-/
theorem ySym_deriv_fun : deriv ySym = ySymPrime := by
  funext t
  have h := (ySym_hasDerivAt t).deriv
  simpa [ySymPrime, Pi.div_apply] using h

/-- NODE HE.TimeScaling.ySym_second_deriv
deps: HE.TimeScaling.ySym_deriv_fun, HE.TimeScaling.ySymPrime_hasDerivAt
statement: second derivative of `y(t)=2 sqrt(q(t))` in the simple endpoint case.
-/
theorem ySym_second_deriv (t : ℝ) :
    deriv (deriv ySym) t = 2 / (Real.sqrt (qSym t))^3 := by
  rw [ySym_deriv_fun]
  exact (ySymPrime_hasDerivAt t).deriv

/-- NODE HE.TimeScaling.solve_ypp_from_cube
deps:
statement: if `y^3 y''=16` and `y≠0`, then `y''=16/y^3`.
-/
theorem solve_ypp_from_cube (y ypp : ℝ) (hy : y^3 ≠ 0) (h : y^3 * ypp = 16) :
    ypp = 16 / y^3 := by
  have hdiv : (y^3 * ypp) / y^3 = 16 / y^3 := by
    rw [h]
  have hleft : (y^3 * ypp) / y^3 = ypp := by
    exact mul_div_cancel_left₀ ypp hy
  rw [hleft] at hdiv
  exact hdiv

/-- NODE HE.TimeScaling.ySym_cube_mul_second_deriv
deps: HE.TimeScaling.ySym_second_deriv, HE.TimeScaling.symmetric_q_pos
statement: in the simple endpoint case, `y^3 y''=16`.
-/
theorem ySym_cube_mul_second_deriv (t : ℝ) :
    (ySym t)^3 * deriv (deriv ySym) t = 16 := by
  rw [ySym_second_deriv]
  unfold ySym
  have hsqrt_ne : Real.sqrt (qSym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (symmetric_q_pos t))
  field_simp [hsqrt_ne]
  ring

/-- NODE HE.TimeScaling.ySym_ode
deps: HE.TimeScaling.ySym_cube_mul_second_deriv, HE.TimeScaling.symmetric_y_cube_ne_zero, HE.TimeScaling.solve_ypp_from_cube
statement: the simple endpoint width satisfies `y''=16/y^3`.
-/
theorem ySym_ode (t : ℝ) :
    deriv (deriv ySym) t = 16 / (ySym t)^3 := by
  apply solve_ypp_from_cube (ySym t) (deriv (deriv ySym) t)
    (symmetric_y_cube_ne_zero t)
  exact ySym_cube_mul_second_deriv t

end TimeScaling
end HardyCompactSupport



