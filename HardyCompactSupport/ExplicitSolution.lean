import Mathlib
import HardyCompactSupport.IntermediateResults

/-!
# Explicit endpoint solution

This file defines the explicit solution and potential and proves the
derivative identities used in the Schrodinger equation and endpoint Gaussian
estimates.
-/

noncomputable section

namespace HardyCompactSupport
namespace ExplicitSolution

/--
Similarity variable for the normalized one-dimensional endpoint construction:
`s = x / y(t)`.
-/
def endpointScale (t x : ℝ) : ℝ :=
  x / TimeScaling.ySym t

/-- Quadratic phase coefficient `b(t)=(2t-1)/(4q(t))`. -/
def endpointB (t : ℝ) : ℝ :=
  (2 * t - 1) / (4 * TimeScaling.qSym t)

/--
The real amplitude of the normalized even endpoint solution in dimension
`n = 1`, with exponent `k = 1`.
-/
def endpointEvenProfile (s : ℝ) : ℝ :=
  Real.exp (-(s^2)) * (1 + s^2)⁻¹

/-- Logarithmic derivative `f'/f` of the even profile. -/
def endpointProfileSlope (s : ℝ) : ℝ :=
  -2 * s * (s^2 + 2) / (1 + s^2)

/-- Derivative of `endpointProfileSlope`. -/
def endpointProfileSlopeDeriv (s : ℝ) : ℝ :=
  -2 * (s^4 + s^2 + 2) / (1 + s^2)^2

/-- Ratio `f''/f` of the even profile. -/
def endpointProfileSecondRatio (s : ℝ) : ℝ :=
  2 * (2 * s^6 + 7 * s^4 + 7 * s^2 - 2) / (1 + s^2)^2

def endpointEvenAmplitude (t x : ℝ) : ℝ :=
  (1 / Real.sqrt (TimeScaling.ySym t)) *
    Real.exp (-(endpointScale t x)^2) *
      (1 + (endpointScale t x)^2)⁻¹

/-- The quadratic phase plus time phase for the same normalized even solution. -/
def endpointEvenPhase (t x : ℝ) : ℝ :=
  ((2 * t - 1) / (4 * TimeScaling.qSym t)) * x^2 +
    (3 / 2) * Real.arctan (2 * t - 1)

/-- Concrete normalized even endpoint solution. -/
def endpointEvenSolution (t x : ℝ) : ℂ :=
  (endpointEvenAmplitude t x : ℂ) *
    Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ))

/-- Complex phase factor `e^{iφ}`. -/
def endpointPhaseFactor (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ))

/-- Spatial logarithmic phase derivative `i φ_x`. -/
def endpointPhaseXFactor (t x : ℝ) : ℂ :=
  Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ)

/-- Spatial derivative of the logarithmic phase derivative `i φ_x`. -/
def endpointPhaseXXFactor (t : ℝ) : ℂ :=
  Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t) : ℝ) : ℂ)

/-- Time logarithmic phase derivative `i φ_t`. -/
def endpointPhaseTFactor (t x : ℝ) : ℂ :=
  Complex.I *
    (((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
      3 / (2 * TimeScaling.qSym t) : ℝ) : ℂ)

/-- Compact formula for the first spatial derivative of the solution. -/
def endpointEvenSolutionX (t x : ℝ) : ℂ :=
  ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x : ℝ) : ℂ) *
    endpointPhaseFactor t x +
  (endpointEvenAmplitude t x : ℂ) *
    (endpointPhaseFactor t x * endpointPhaseXFactor t x)

/-- Compact formula for the second spatial derivative of the solution. -/
def endpointEvenSolutionXX (t x : ℝ) : ℂ :=
  ((deriv (deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ)) x : ℝ) : ℂ) *
    endpointPhaseFactor t x +
  ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x : ℝ) : ℂ) *
    (endpointPhaseFactor t x * endpointPhaseXFactor t x) +
  ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x : ℝ) : ℂ) *
    (endpointPhaseFactor t x * endpointPhaseXFactor t x) +
  (endpointEvenAmplitude t x : ℂ) *
    ((endpointPhaseFactor t x * endpointPhaseXFactor t x) *
      endpointPhaseXFactor t x +
    endpointPhaseFactor t x * endpointPhaseXXFactor t)

/-- Compact formula for the first time derivative of the solution. -/
def endpointEvenSolutionT (t x : ℝ) : ℂ :=
  ((deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t : ℝ) : ℂ) *
    endpointPhaseFactor t x +
  (endpointEvenAmplitude t x : ℂ) *
    (endpointPhaseFactor t x * endpointPhaseTFactor t x)

/--
Concrete normalized even endpoint potential from the report formula with
`n = 1`, `k = 1`:
`V_N = -(s^2+5)/(2 q (1+s^2)^2)`.
-/
def endpointEvenPotential (t x : ℝ) : ℝ :=
  - ((endpointScale t x)^2 + 5) /
    (2 * TimeScaling.qSym t * (1 + (endpointScale t x)^2)^2)

/-- Concrete construction of the endpoint solution `u`. -/
def ConcreteSolutionDefined : Prop :=
  endpointEvenSolution 0 0 ≠ 0 ∧
    ∀ t : ℝ,
      deriv (deriv TimeScaling.ySym) t = 16 / (TimeScaling.ySym t)^3

/-- Concrete construction of the real bounded scalar potential `V`. -/
def ConcretePotentialDefined : Prop :=
  ∀ t x : ℝ, |endpointEvenPotential t x| ≤ 5

/-- Pointwise one-dimensional Schrödinger residual for the concrete pair. -/
def schrodingerResidual (t x : ℝ) : ℂ :=
  Complex.I * deriv (fun τ : ℝ => endpointEvenSolution τ x) t +
    deriv (deriv (fun ξ : ℝ => endpointEvenSolution t ξ)) x -
      (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x

/-- The constructed pair satisfies the Schrödinger equation. -/
def FullSchrodingerEquation : Prop :=
  ∀ t x : ℝ, schrodingerResidual t x = 0

/--
Endpoint Gaussian `L^2` certificate for the concrete one-dimensional even
solution.  The weighted endpoint squares are dominated by the integrable
standard tail `8/(1+x^2)`.
-/
structure FullEndpointGaussianL2 : Prop where
  zero_weighted_square_bound :
    ∀ x : ℝ,
      (Real.exp (x^2 / 4) * endpointEvenAmplitude 0 x)^2 ≤
        8 / (1 + x^2)
  one_weighted_square_bound :
    ∀ x : ℝ,
      (Real.exp (x^2 / 4) * endpointEvenAmplitude 1 x)^2 ≤
        8 / (1 + x^2)
  controlling_tail_integrable :
    MeasureTheory.Integrable (fun x : ℝ => 8 / (1 + x^2))

/-- The final fully semantic real scalar endpoint theorem. -/
structure FullRealScalarEndpoint : Prop where
  solution_defined : ConcreteSolutionDefined
  potential_defined : ConcretePotentialDefined
  schrodinger_equation : FullSchrodingerEquation
  endpoint_gaussian_L2 : FullEndpointGaussianL2
  algebraic_claim : ConstructionStatement.RealScalarEndpointClaim

/-! ## Nontriviality and the bounded real scalar potential -/

/-- NODE HE.ExplicitSolution.endpoint_amplitude_nonzero
deps: HE.TimeScaling.symmetric_y_pos
statement: the concrete even endpoint amplitude is nonzero.
-/
theorem endpoint_amplitude_nonzero (t x : ℝ) :
    endpointEvenAmplitude t x ≠ 0 := by
  unfold endpointEvenAmplitude
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply div_ne_zero
      · norm_num
      · exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos t))
    · exact Real.exp_ne_zero _
  · apply inv_ne_zero
    exact ne_of_gt (by positivity : 0 < 1 + (endpointScale t x)^2)

/-- NODE HE.ExplicitSolution.endpoint_solution_nonzero
deps: HE.ExplicitSolution.endpoint_amplitude_nonzero
statement: the concrete endpoint solution is nonzero at the origin.
-/
theorem endpoint_solution_nonzero : endpointEvenSolution 0 0 ≠ 0 := by
  unfold endpointEvenSolution
  apply mul_ne_zero
  · exact_mod_cast endpoint_amplitude_nonzero 0 0
  · exact Complex.exp_ne_zero _

/-- NODE HE.ExplicitSolution.qSym_half_le
deps:
statement: the normalized quadratic satisfies `q(t) ≥ 1/2`.
-/
theorem qSym_half_le (t : ℝ) : (1 / 2 : ℝ) ≤ TimeScaling.qSym t := by
  unfold TimeScaling.qSym
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]

/-- NODE HE.ExplicitSolution.rational_tail_bound
deps:
statement: the normalized rational tail `(z+5)/(1+z)^2` is bounded by `5` on `z≥0`.
-/
theorem rational_tail_bound (z : ℝ) (hz : 0 ≤ z) :
    (z + 5) / (1 + z)^2 ≤ 5 := by
  have hpos : 0 < (1 + z)^2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg z]

/-- NODE HE.ExplicitSolution.even_potential_bound
deps: HE.ExplicitSolution.qSym_half_le, HE.ExplicitSolution.rational_tail_bound
statement: the concrete normalized even potential is globally bounded by `5`.
-/
theorem even_potential_bound (t x : ℝ) : |endpointEvenPotential t x| ≤ 5 := by
  unfold endpointEvenPotential
  set z : ℝ := (endpointScale t x)^2
  change |-(z + 5) / (2 * TimeScaling.qSym t * (1 + z)^2)| ≤ 5
  rw [neg_div, abs_neg]
  have hz : 0 ≤ z := by
    rw [show z = (endpointScale t x)^2 by exact rfl]
    exact sq_nonneg (endpointScale t x)
  have hqhalf : (1 / 2 : ℝ) ≤ TimeScaling.qSym t := qSym_half_le t
  have hnonneg : 0 ≤ (z + 5) / (2 * TimeScaling.qSym t * (1 + z)^2) := by
    positivity
  rw [abs_of_nonneg hnonneg]
  have hden_ge : (1 + z)^2 ≤ 2 * TimeScaling.qSym t * (1 + z)^2 := by
    nlinarith [sq_nonneg (1 + z), hqhalf]
  have h1 :
      (z + 5) / (2 * TimeScaling.qSym t * (1 + z)^2) ≤
        (z + 5) / (1 + z)^2 := by
    apply div_le_div_of_nonneg_left
    · nlinarith
    · positivity
    · exact hden_ge
  exact le_trans h1 (rational_tail_bound z hz)

/-! ## Width, phase, and similarity-variable derivatives -/

/-- NODE HE.ExplicitSolution.endpointB_deriv
deps: HE.TimeScaling.qSym_deriv, HE.TimeScaling.qSym_hasDerivAt, HE.TimeScaling.symmetric_q_ne_zero
statement: derivative of the quadratic phase coefficient `b(t)`.
-/
theorem endpointB_deriv (t : ℝ) :
    deriv endpointB t = t * (1 - t) / (TimeScaling.qSym t)^2 := by
  unfold endpointB
  change deriv ((fun τ : ℝ => 2 * τ - 1) / fun τ => 4 * TimeScaling.qSym τ) t =
    t * (1 - t) / (TimeScaling.qSym t)^2
  rw [deriv_div]
  · rw [show deriv (fun τ : ℝ => 2 * τ - 1) t = 2 by simp]
    rw [show deriv (fun τ : ℝ => 4 * TimeScaling.qSym τ) t = 4 * (4 * t - 2) by
      rw [deriv_const_mul]
      · rw [TimeScaling.qSym_deriv]
      · exact (TimeScaling.qSym_hasDerivAt t).differentiableAt]
    have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
    unfold TimeScaling.qSym at hq ⊢
    field_simp [hq]
    ring
  · fun_prop
  · exact (TimeScaling.qSym_hasDerivAt t).differentiableAt.const_mul 4
  · exact mul_ne_zero (by norm_num) (TimeScaling.symmetric_q_ne_zero t)

theorem endpointB_differentiableAt (t : ℝ) : DifferentiableAt ℝ endpointB t := by
  unfold endpointB
  apply DifferentiableAt.div
  · fun_prop
  · exact (TimeScaling.qSym_hasDerivAt t).differentiableAt.const_mul 4
  · exact mul_ne_zero (by norm_num) (TimeScaling.symmetric_q_ne_zero t)

/-- NODE HE.ExplicitSolution.endpointB_width_transport
deps: HE.TimeScaling.ySym_deriv_fun, HE.TimeScaling.symmetric_sqrt_sq, HE.TimeScaling.symmetric_q_pos
statement: the phase coefficient satisfies the transport identity `4 b(t)y(t)=y'(t)`.
-/
theorem endpointB_width_transport (t : ℝ) :
    4 * endpointB t * TimeScaling.ySym t = deriv TimeScaling.ySym t := by
  rw [TimeScaling.ySym_deriv_fun]
  unfold endpointB TimeScaling.ySym TimeScaling.ySymPrime
  simp [Pi.div_apply]
  set q : ℝ := TimeScaling.qSym t
  set r : ℝ := Real.sqrt q
  have hr : r ≠ 0 := by
    dsimp [r, q]
    exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_q_pos t))
  have hqr : r^2 = q := by
    dsimp [r, q]
    exact TimeScaling.symmetric_sqrt_sq t
  change 4 * ((2 * t - 1) / (4 * q)) * (2 * r) = (4 * t - 2) / r
  rw [← hqr]
  field_simp [hr]
  ring

/-- NODE HE.ExplicitSolution.phase_x_deriv
deps:
statement: first spatial derivative of the concrete quadratic phase.
-/
theorem phase_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenPhase t ξ) x =
      ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x := by
  unfold endpointEvenPhase
  change deriv (((fun ξ : ℝ =>
      ((2 * t - 1) / (4 * TimeScaling.qSym t)) * ξ ^ 2) +
        (fun _ : ℝ => (3 / 2) * Real.arctan (2 * t - 1)))) x =
    ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x
  rw [deriv_add]
  · rw [deriv_const_mul]
    · simp
      ring
    · fun_prop
  · fun_prop
  · fun_prop

/-- NODE HE.ExplicitSolution.phase_x_second_deriv
deps: HE.ExplicitSolution.phase_x_deriv
statement: second spatial derivative of the concrete quadratic phase.
-/
theorem phase_x_second_deriv (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointEvenPhase t ξ)) x =
      (2 * t - 1) / (2 * TimeScaling.qSym t) := by
  have hfun : deriv (fun ξ : ℝ => endpointEvenPhase t ξ) =
      fun x : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x := by
    funext x
    exact phase_x_deriv t x
  rw [hfun]
  simp

/-- NODE HE.ExplicitSolution.phase_x_complex_deriv
deps: HE.ExplicitSolution.phase_x_deriv
statement: complex-valued spatial derivative of the real phase.
-/
theorem phase_x_complex_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => (endpointEvenPhase t ξ : ℂ)) x =
      (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ) := by
  have hdiff : DifferentiableAt ℝ (fun ξ : ℝ => endpointEvenPhase t ξ) x := by
    unfold endpointEvenPhase
    fun_prop
  have hderiv : HasDerivAt (fun ξ : ℝ => endpointEvenPhase t ξ)
      (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) x := by
    simpa [phase_x_deriv t x] using hdiff.hasDerivAt
  simpa using hderiv.ofReal_comp.deriv

/-- NODE HE.ExplicitSolution.phaseExp_x_deriv
deps: HE.ExplicitSolution.phase_x_complex_deriv
statement: spatial derivative of the complex phase factor `exp(i φ)`.
-/
theorem phaseExp_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ =>
        Complex.exp (Complex.I * (endpointEvenPhase t ξ : ℂ))) x =
      Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
        (Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ)) := by
  have hdiffPhase : DifferentiableAt ℝ
      (fun ξ : ℝ => (endpointEvenPhase t ξ : ℂ)) x := by
    have hreal : DifferentiableAt ℝ (fun ξ : ℝ => endpointEvenPhase t ξ) x := by
      unfold endpointEvenPhase
      fun_prop
    have hderiv : HasDerivAt (fun ξ : ℝ => endpointEvenPhase t ξ)
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) x := by
      simpa [phase_x_deriv t x] using hreal.hasDerivAt
    exact hderiv.ofReal_comp.differentiableAt
  have hdiffInner : DifferentiableAt ℝ
      (fun ξ : ℝ => Complex.I * (endpointEvenPhase t ξ : ℂ)) x :=
    hdiffPhase.const_mul Complex.I
  calc
    deriv (fun ξ : ℝ =>
        Complex.exp (Complex.I * (endpointEvenPhase t ξ : ℂ))) x =
        Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
          deriv (fun ξ : ℝ => Complex.I * (endpointEvenPhase t ξ : ℂ)) x := by
          simpa using (deriv_cexp hdiffInner)
    _ = Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
        (Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ)) := by
          rw [deriv_const_mul Complex.I hdiffPhase]
          rw [phase_x_complex_deriv]

/-- NODE HE.ExplicitSolution.endpointPhaseFactor_x_deriv
deps: HE.ExplicitSolution.phaseExp_x_deriv
statement: compact spatial derivative of the complex phase factor.
-/
theorem endpointPhaseFactor_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointPhaseFactor t ξ) x =
      endpointPhaseFactor t x * endpointPhaseXFactor t x := by
  unfold endpointPhaseFactor endpointPhaseXFactor
  exact phaseExp_x_deriv t x

/-- NODE HE.ExplicitSolution.endpointPhaseXFactor_x_deriv
deps:
statement: spatial derivative of the logarithmic phase derivative `i φ_x`.
-/
theorem endpointPhaseXFactor_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointPhaseXFactor t ξ) x =
      endpointPhaseXXFactor t := by
  unfold endpointPhaseXFactor endpointPhaseXXFactor
  have hreal : DifferentiableAt ℝ
      (fun ξ : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ) x := by
    fun_prop
  have hcomplex : DifferentiableAt ℝ
      (fun ξ : ℝ => (((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ : ℂ)) x := by
    simpa using hreal.hasDerivAt.ofReal_comp.differentiableAt
  rw [deriv_const_mul Complex.I hcomplex]
  have hderiv : deriv
      (fun ξ : ℝ => (((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ : ℂ)) x =
        (((2 * t - 1) / (2 * TimeScaling.qSym t) : ℝ) : ℂ) := by
    have hrealDeriv :
        deriv (fun ξ : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ) x =
          ((2 * t - 1) / (2 * TimeScaling.qSym t)) := by
      simp
    simpa [hrealDeriv] using hreal.hasDerivAt.ofReal_comp.deriv
  rw [hderiv]

/-- NODE HE.ExplicitSolution.phase_x_width_form
deps: HE.TimeScaling.ySym_deriv_fun, HE.TimeScaling.symmetric_q_ne_zero, HE.TimeScaling.symmetric_q_pos
statement: real spatial phase derivative in width variables.
-/
theorem phase_x_width_form (t x : ℝ) :
    ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x =
      endpointScale t x * deriv TimeScaling.ySym t / 2 := by
  rw [TimeScaling.ySym_deriv_fun]
  unfold endpointScale TimeScaling.ySymPrime TimeScaling.ySym
  simp [Pi.div_apply]
  have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
  have hsqrt_ne : Real.sqrt (TimeScaling.qSym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_q_pos t))
  have hsqrt_sq : (Real.sqrt (TimeScaling.qSym t))^2 =
      TimeScaling.qSym t := TimeScaling.symmetric_sqrt_sq t
  field_simp [hq, hsqrt_ne]
  rw [hsqrt_sq]
  ring

/-- NODE HE.ExplicitSolution.phase_xx_width_form
deps: HE.TimeScaling.ySym_deriv_fun, HE.TimeScaling.symmetric_q_ne_zero, HE.TimeScaling.symmetric_q_pos
statement: real second spatial phase derivative in width variables.
-/
theorem phase_xx_width_form (t : ℝ) :
    (2 * t - 1) / (2 * TimeScaling.qSym t) =
      deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t) := by
  rw [TimeScaling.ySym_deriv_fun]
  unfold TimeScaling.ySymPrime TimeScaling.ySym
  simp [Pi.div_apply]
  have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
  have hsqrt_ne : Real.sqrt (TimeScaling.qSym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_q_pos t))
  have hsqrt_sq : (Real.sqrt (TimeScaling.qSym t))^2 =
      TimeScaling.qSym t := TimeScaling.symmetric_sqrt_sq t
  field_simp [hq, hsqrt_ne]
  rw [hsqrt_sq]
  ring

/-- NODE HE.ExplicitSolution.endpointPhaseXFactor_width_form
deps: HE.ExplicitSolution.phase_x_width_form
statement: complex spatial logarithmic phase derivative in width variables.
-/
theorem endpointPhaseXFactor_width_form (t x : ℝ) :
    endpointPhaseXFactor t x =
      Complex.I * ((endpointScale t x * deriv TimeScaling.ySym t / 2 : ℝ) : ℂ) := by
  unfold endpointPhaseXFactor
  rw [show (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ) =
      ((endpointScale t x * deriv TimeScaling.ySym t / 2 : ℝ) : ℂ) by
        exact_mod_cast phase_x_width_form t x]

/-- NODE HE.ExplicitSolution.endpointPhaseXXFactor_width_form
deps: HE.ExplicitSolution.phase_xx_width_form
statement: complex second spatial logarithmic phase derivative in width variables.
-/
theorem endpointPhaseXXFactor_width_form (t : ℝ) :
    endpointPhaseXXFactor t =
      Complex.I * ((deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t) : ℝ) : ℂ) := by
  unfold endpointPhaseXXFactor
  rw [show (((2 * t - 1) / (2 * TimeScaling.qSym t) : ℝ) : ℂ) =
      ((deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t) : ℝ) : ℂ) by
        exact_mod_cast phase_xx_width_form t]

/-- NODE HE.ExplicitSolution.phase_energy_width_identity
deps: HE.TimeScaling.symmetric_y_sq, HE.TimeScaling.symmetric_q_ne_zero, HE.TimeScaling.symmetric_y_ne_zero
statement: the real phase energy `φ_t + φ_x^2` in width variables.
-/
theorem phase_energy_width_identity (t x : ℝ) :
    ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        3 / (2 * TimeScaling.qSym t)) +
      (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 =
      (4 * (endpointScale t x)^2 + 6) / (TimeScaling.ySym t)^2 := by
  unfold endpointScale
  set q : ℝ := TimeScaling.qSym t
  set y : ℝ := TimeScaling.ySym t
  have hq : q ≠ 0 := by
    dsimp [q]
    exact TimeScaling.symmetric_q_ne_zero t
  have hy : y ≠ 0 := by
    dsimp [y]
    exact TimeScaling.symmetric_y_ne_zero t
  have hy_sq : y^2 = 4 * q := by
    dsimp [y, q]
    exact TimeScaling.symmetric_y_sq t
  change ((t * (1 - t) / q^2) * x^2 + 3 / (2 * q)) +
      (((2 * t - 1) / (2 * q)) * x)^2 = (4 * (x / y)^2 + 6) / y^2
  field_simp [hq, hy]
  have hy4 : y^4 = (4 * q)^2 := by nlinarith [hy_sq]
  rw [hy4, hy_sq]
  subst q
  ring

/-- NODE HE.ExplicitSolution.endpointPhaseFactor_mul_xFactor_x_deriv
deps: HE.ExplicitSolution.endpointPhaseFactor_x_deriv, HE.ExplicitSolution.endpointPhaseXFactor_x_deriv
statement: spatial derivative of `e^{iφ} * iφ_x`.
-/
theorem endpointPhaseFactor_mul_xFactor_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointPhaseFactor t ξ * endpointPhaseXFactor t ξ) x =
      (endpointPhaseFactor t x * endpointPhaseXFactor t x) *
        endpointPhaseXFactor t x +
      endpointPhaseFactor t x * endpointPhaseXXFactor t := by
  have hdiffPhase : DifferentiableAt ℝ
      (fun ξ : ℝ => endpointPhaseFactor t ξ) x := by
    unfold endpointPhaseFactor
    have hreal : DifferentiableAt ℝ (fun ξ : ℝ => endpointEvenPhase t ξ) x := by
      unfold endpointEvenPhase
      fun_prop
    have hcomplex : DifferentiableAt ℝ
        (fun ξ : ℝ => (endpointEvenPhase t ξ : ℂ)) x :=
      hreal.hasDerivAt.ofReal_comp.differentiableAt
    exact (hcomplex.const_mul Complex.I).cexp
  have hdiffX : DifferentiableAt ℝ
      (fun ξ : ℝ => endpointPhaseXFactor t ξ) x := by
    unfold endpointPhaseXFactor
    have hreal : DifferentiableAt ℝ
        (fun ξ : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ) x := by
      fun_prop
    have hcomplex : DifferentiableAt ℝ
        (fun ξ : ℝ => (((2 * t - 1) / (2 * TimeScaling.qSym t)) * ξ : ℂ)) x := by
      simpa using hreal.hasDerivAt.ofReal_comp.differentiableAt
    exact hcomplex.const_mul Complex.I
  rw [deriv_fun_mul hdiffPhase hdiffX]
  rw [endpointPhaseFactor_x_deriv, endpointPhaseXFactor_x_deriv]

/-- NODE HE.ExplicitSolution.phase_t_deriv
deps: HE.ExplicitSolution.endpointB_deriv
statement: time derivative of the concrete quadratic phase.
-/
theorem phase_t_deriv (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenPhase τ x) t =
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        3 / (2 * TimeScaling.qSym t) := by
  unfold endpointEvenPhase
  change deriv (((fun τ : ℝ => endpointB τ * x^2) +
    (fun τ : ℝ => (3 / 2) * Real.arctan (2 * τ - 1)))) t =
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        3 / (2 * TimeScaling.qSym t)
  rw [deriv_add]
  · rw [deriv_mul_const]
    · rw [endpointB_deriv]
      rw [deriv_const_mul]
      · rw [deriv_arctan]
        · rw [show deriv (fun τ : ℝ => 2 * τ - 1) t = 2 by simp]
          have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
          unfold TimeScaling.qSym at hq ⊢
          field_simp [hq]
          ring
        · fun_prop
      · exact (show DifferentiableAt ℝ
          (fun τ : ℝ => Real.arctan (2 * τ - 1)) t from by
            exact (show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
              fun_prop).arctan)
    · exact endpointB_differentiableAt t
  · exact (endpointB_differentiableAt t).mul (differentiableAt_const _)
  · exact ((show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
      fun_prop).arctan).const_mul (3 / 2)

/-- NODE HE.ExplicitSolution.phase_t_complex_deriv
deps: HE.ExplicitSolution.phase_t_deriv
statement: complex-valued time derivative of the real phase.
-/
theorem phase_t_complex_deriv (t x : ℝ) :
    deriv (fun τ : ℝ => (endpointEvenPhase τ x : ℂ)) t =
      (((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        3 / (2 * TimeScaling.qSym t) : ℝ) : ℂ) := by
  have hdiff : DifferentiableAt ℝ (fun τ : ℝ => endpointEvenPhase τ x) t := by
    unfold endpointEvenPhase
    exact ((endpointB_differentiableAt t).mul (differentiableAt_const _)).add
      (((show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
        fun_prop).arctan).const_mul (3 / 2))
  have hderiv : HasDerivAt (fun τ : ℝ => endpointEvenPhase τ x)
      ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        3 / (2 * TimeScaling.qSym t)) t := by
    simpa [phase_t_deriv t x] using hdiff.hasDerivAt
  simpa using hderiv.ofReal_comp.deriv

/-- NODE HE.ExplicitSolution.phaseExp_t_deriv
deps: HE.ExplicitSolution.phase_t_complex_deriv
statement: time derivative of the complex phase factor `exp(i φ)`.
-/
theorem phaseExp_t_deriv (t x : ℝ) :
    deriv (fun τ : ℝ =>
        Complex.exp (Complex.I * (endpointEvenPhase τ x : ℂ))) t =
      Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
        (Complex.I *
          (((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
            3 / (2 * TimeScaling.qSym t) : ℝ) : ℂ)) := by
  have hdiffPhase : DifferentiableAt ℝ
      (fun τ : ℝ => (endpointEvenPhase τ x : ℂ)) t := by
    have hreal : DifferentiableAt ℝ (fun τ : ℝ => endpointEvenPhase τ x) t := by
      unfold endpointEvenPhase
      exact ((endpointB_differentiableAt t).mul (differentiableAt_const _)).add
        (((show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
          fun_prop).arctan).const_mul (3 / 2))
    have hderiv : HasDerivAt (fun τ : ℝ => endpointEvenPhase τ x)
        ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          3 / (2 * TimeScaling.qSym t)) t := by
      simpa [phase_t_deriv t x] using hreal.hasDerivAt
    exact hderiv.ofReal_comp.differentiableAt
  have hdiffInner : DifferentiableAt ℝ
      (fun τ : ℝ => Complex.I * (endpointEvenPhase τ x : ℂ)) t :=
    hdiffPhase.const_mul Complex.I
  calc
    deriv (fun τ : ℝ =>
        Complex.exp (Complex.I * (endpointEvenPhase τ x : ℂ))) t =
        Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
          deriv (fun τ : ℝ => Complex.I * (endpointEvenPhase τ x : ℂ)) t := by
          simpa using (deriv_cexp hdiffInner)
    _ = Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
        (Complex.I *
          (((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
            3 / (2 * TimeScaling.qSym t) : ℝ) : ℂ)) := by
          rw [deriv_const_mul Complex.I hdiffPhase]
          rw [phase_t_complex_deriv]

/-- NODE HE.ExplicitSolution.endpointScale_x_deriv
deps: HE.TimeScaling.symmetric_y_ne_zero
statement: spatial derivative of the similarity variable `s=x/y(t)`.
-/
theorem endpointScale_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointScale t ξ) x =
      1 / TimeScaling.ySym t := by
  unfold endpointScale
  rw [deriv_div_const]
  simp

/-- NODE HE.ExplicitSolution.endpointScale_x_second_deriv
deps: HE.ExplicitSolution.endpointScale_x_deriv
statement: second spatial derivative of the similarity variable vanishes.
-/
theorem endpointScale_x_second_deriv (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointScale t ξ)) x = 0 := by
  have hfun : deriv (fun ξ : ℝ => endpointScale t ξ) =
      fun _ : ℝ => 1 / TimeScaling.ySym t := by
    funext ξ
    exact endpointScale_x_deriv t ξ
  rw [hfun]
  simp

/-- NODE HE.ExplicitSolution.endpointScale_t_deriv
deps: HE.TimeScaling.ySym_hasDerivAt, HE.TimeScaling.symmetric_y_ne_zero
statement: time derivative of the similarity variable `s=x/y(t)`.
-/
theorem endpointScale_t_deriv (t x : ℝ) :
    deriv (fun τ : ℝ => endpointScale τ x) t =
      - x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2 := by
  unfold endpointScale
  simpa using
    (deriv_const_div x (TimeScaling.ySym_hasDerivAt t).differentiableAt
      (TimeScaling.symmetric_y_ne_zero t))

/-- NODE HE.ExplicitSolution.endpointScale_differentiableAt_t
deps: HE.TimeScaling.ySym_hasDerivAt, HE.TimeScaling.symmetric_y_ne_zero
statement: the similarity variable is differentiable in time.
-/
theorem endpointScale_differentiableAt_t (t x : ℝ) :
    DifferentiableAt ℝ (fun τ : ℝ => endpointScale τ x) t := by
  unfold endpointScale
  exact (differentiableAt_const x).div
    (TimeScaling.ySym_hasDerivAt t).differentiableAt
    (TimeScaling.symmetric_y_ne_zero t)

/-- NODE HE.ExplicitSolution.endpointWidthFactor_t_deriv
deps: HE.TimeScaling.ySym_hasDerivAt, HE.TimeScaling.symmetric_y_ne_zero, HE.TimeScaling.symmetric_y_pos
statement: derivative of the width factor `1/sqrt(y(t))`.
-/
theorem endpointWidthFactor_t_deriv (t : ℝ) :
    deriv (fun τ : ℝ => 1 / Real.sqrt (TimeScaling.ySym τ)) t =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        (-(deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t))) := by
  have hy : TimeScaling.ySym t ≠ 0 := TimeScaling.symmetric_y_ne_zero t
  have hypos : 0 < TimeScaling.ySym t := TimeScaling.symmetric_y_pos t
  have hsqrt_ne : Real.sqrt (TimeScaling.ySym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hypos)
  have hdiffSqrt : DifferentiableAt ℝ
      (fun τ : ℝ => Real.sqrt (TimeScaling.ySym τ)) t :=
    (TimeScaling.ySym_hasDerivAt t).differentiableAt.sqrt hy
  rw [deriv_const_div (1 : ℝ) hdiffSqrt hsqrt_ne]
  have hsqrt_deriv :
      deriv (fun τ : ℝ => Real.sqrt (TimeScaling.ySym τ)) t =
        deriv TimeScaling.ySym t / (2 * Real.sqrt (TimeScaling.ySym t)) := by
    rw [deriv_sqrt (TimeScaling.ySym_hasDerivAt t).differentiableAt hy]
  rw [hsqrt_deriv]
  have hsqrt_sq : (Real.sqrt (TimeScaling.ySym t))^2 =
      TimeScaling.ySym t := by
    rw [Real.sq_sqrt]
    exact le_of_lt hypos
  field_simp [hsqrt_ne, hy]
  rw [hsqrt_sq]

/-- NODE HE.ExplicitSolution.endpointScale_sq_x_deriv
deps: HE.ExplicitSolution.endpointScale_x_deriv
statement: spatial derivative of the squared similarity variable.
-/
theorem endpointScale_sq_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => (endpointScale t ξ)^2) x =
      2 * endpointScale t x / TimeScaling.ySym t := by
  change deriv ((fun ξ : ℝ => endpointScale t ξ)^2) x =
      2 * endpointScale t x / TimeScaling.ySym t
  rw [deriv_pow]
  · rw [endpointScale_x_deriv]
    ring
  · unfold endpointScale
    fun_prop

/-- NODE HE.ExplicitSolution.endpointScale_sq_x_second_deriv
deps: HE.ExplicitSolution.endpointScale_sq_x_deriv, HE.ExplicitSolution.endpointScale_x_deriv, HE.TimeScaling.symmetric_y_ne_zero
statement: second spatial derivative of the squared similarity variable.
-/
theorem endpointScale_sq_x_second_deriv (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => (endpointScale t ξ)^2)) x =
      2 / (TimeScaling.ySym t)^2 := by
  have hfun : deriv (fun ξ : ℝ => (endpointScale t ξ)^2) =
      fun ξ : ℝ => 2 * endpointScale t ξ / TimeScaling.ySym t := by
    funext ξ
    exact endpointScale_sq_x_deriv t ξ
  rw [hfun]
  rw [deriv_div_const]
  rw [deriv_const_mul]
  · rw [endpointScale_x_deriv]
    field_simp [TimeScaling.symmetric_y_ne_zero t]
  · unfold endpointScale
    fun_prop

/-! ## Profile and amplitude derivatives -/

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_profile
deps:
statement: the concrete amplitude is a width factor times the even profile in `s=x/y(t)`.
-/
theorem endpointEvenAmplitude_profile (t x : ℝ) :
    endpointEvenAmplitude t x =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        endpointEvenProfile (endpointScale t x) := by
  unfold endpointEvenAmplitude endpointEvenProfile
  ring

/-- NODE HE.ExplicitSolution.endpointEvenProfile_deriv
deps:
statement: first derivative of the even profile as `f' = f * L`.
-/
theorem endpointEvenProfile_deriv (s : ℝ) :
    deriv endpointEvenProfile s =
      endpointEvenProfile s * endpointProfileSlope s := by
  unfold endpointEvenProfile endpointProfileSlope
  have hbase : 1 + s^2 ≠ 0 := by positivity
  have hExpDiff : DifferentiableAt ℝ (fun x : ℝ => Real.exp (-(x ^ 2))) s := by
    fun_prop
  have hRatDiff : DifferentiableAt ℝ (fun x : ℝ => (1 + x^2)⁻¹) s := by
    apply DifferentiableAt.inv
    · fun_prop
    · positivity
  rw [deriv_fun_mul hExpDiff hRatDiff]
  have hExpDeriv :
      deriv (fun x : ℝ => Real.exp (-(x ^ 2))) s =
        Real.exp (-(s^2)) * (-2 * s) := by
    have hinnerDiff : DifferentiableAt ℝ (fun x : ℝ => -(x^2)) s := by
      fun_prop
    rw [deriv_exp hinnerDiff]
    have hinner : deriv (fun x : ℝ => -(x^2)) s = -2 * s := by
      rw [show deriv (fun x : ℝ => -(x^2)) s =
          - deriv (fun x : ℝ => x^2) s by
            exact (deriv.neg (f := fun x : ℝ => x^2) (x := s))]
      simp
    rw [hinner]
  have hRatDeriv :
      deriv (fun x : ℝ => (1 + x^2)⁻¹) s =
        -(2 * s) / (1 + s^2)^2 := by
    have hdiff : DifferentiableAt ℝ (fun x : ℝ => 1 + x^2) s := by
      fun_prop
    rw [deriv_fun_inv'' hdiff hbase]
    have hinner : deriv (fun x : ℝ => 1 + x^2) s = 2 * s := by
      rw [deriv_const_add]
      simp
    rw [hinner]
  rw [hExpDeriv, hRatDeriv]
  field_simp [hbase]
  ring

/-- NODE HE.ExplicitSolution.endpointProfileSlope_deriv
deps:
statement: derivative of the logarithmic profile slope.
-/
theorem endpointProfileSlope_deriv (s : ℝ) :
    deriv endpointProfileSlope s = endpointProfileSlopeDeriv s := by
  unfold endpointProfileSlope endpointProfileSlopeDeriv
  have hbase : 1 + s^2 ≠ 0 := by positivity
  have hnumDiff : DifferentiableAt ℝ
      (fun x : ℝ => -2 * x * (x^2 + 2)) s := by
    fun_prop
  have hdenDiff : DifferentiableAt ℝ (fun x : ℝ => 1 + x^2) s := by
    fun_prop
  rw [deriv_fun_div hnumDiff hdenDiff hbase]
  have hnum :
      deriv (fun x : ℝ => -2 * x * (x^2 + 2)) s =
        -2 * (s^2 + 2) + (-2 * s) * (2 * s) := by
    rw [deriv_fun_mul]
    · rw [deriv_const_mul]
      · rw [show deriv (fun x : ℝ => x^2 + 2) s = 2 * s by
          rw [deriv_add_const]
          simp]
        simp
      · fun_prop
    · fun_prop
    · fun_prop
  have hdeniv : deriv (fun x : ℝ => 1 + x^2) s = 2 * s := by
    rw [deriv_const_add]
    simp
  rw [hnum, hdeniv]
  field_simp [hbase]
  ring

/-- NODE HE.ExplicitSolution.endpointEvenProfile_second_deriv
deps: HE.ExplicitSolution.endpointEvenProfile_deriv, HE.ExplicitSolution.endpointProfileSlope_deriv
statement: second derivative of the even profile as `f'' = f * M`.
-/
theorem endpointEvenProfile_second_deriv (s : ℝ) :
    deriv (deriv endpointEvenProfile) s =
      endpointEvenProfile s * endpointProfileSecondRatio s := by
  have hfun : deriv endpointEvenProfile =
      fun z : ℝ => endpointEvenProfile z * endpointProfileSlope z := by
    funext z
    exact endpointEvenProfile_deriv z
  rw [hfun]
  have hProfileDiff : DifferentiableAt ℝ endpointEvenProfile s := by
    unfold endpointEvenProfile
    apply DifferentiableAt.mul
    · fun_prop
    · apply DifferentiableAt.inv
      · fun_prop
      · positivity
  have hSlopeDiff : DifferentiableAt ℝ endpointProfileSlope s := by
    unfold endpointProfileSlope
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · positivity
  rw [deriv_fun_mul hProfileDiff hSlopeDiff]
  rw [endpointEvenProfile_deriv, endpointProfileSlope_deriv]
  unfold endpointProfileSlope endpointProfileSlopeDeriv endpointProfileSecondRatio
  field_simp [show 1 + s^2 ≠ 0 by positivity]
  ring

/-- NODE HE.ExplicitSolution.endpointEvenProfile_mul_slope_deriv
deps: HE.ExplicitSolution.endpointEvenProfile_second_deriv, HE.ExplicitSolution.endpointEvenProfile_deriv
statement: derivative of `f * L` is `f * M`.
-/
theorem endpointEvenProfile_mul_slope_deriv (s : ℝ) :
    deriv (fun z : ℝ => endpointEvenProfile z * endpointProfileSlope z) s =
      endpointEvenProfile s * endpointProfileSecondRatio s := by
  have hfun : deriv endpointEvenProfile =
      fun z : ℝ => endpointEvenProfile z * endpointProfileSlope z := by
    funext z
    exact endpointEvenProfile_deriv z
  simpa [hfun] using endpointEvenProfile_second_deriv s

/-- NODE HE.ExplicitSolution.endpointProfile_real_identity
deps:
statement: rational identity behind the real part of the residual.
-/
theorem endpointProfile_real_identity (s : ℝ) :
    endpointProfileSecondRatio s - (4 * s^2 + 6) +
      2 * (s^2 + 5) / (1 + s^2)^2 = 0 := by
  unfold endpointProfileSecondRatio
  have h : 1 + s^2 ≠ 0 := by positivity
  field_simp [h]
  ring

/-- NODE HE.ExplicitSolution.endpointExpFactor_x_deriv
deps: HE.ExplicitSolution.endpointScale_sq_x_deriv
statement: spatial derivative of the Gaussian factor in the even profile.
-/
theorem endpointExpFactor_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => Real.exp (-(endpointScale t ξ)^2)) x =
      Real.exp (-(endpointScale t x)^2) *
        (-(2 * endpointScale t x / TimeScaling.ySym t)) := by
  have hdiff : DifferentiableAt ℝ
      (fun ξ : ℝ => -(endpointScale t ξ)^2) x := by
    unfold endpointScale
    fun_prop
  have hinner :
      deriv (fun ξ : ℝ => -(endpointScale t ξ)^2) x =
        -(2 * endpointScale t x / TimeScaling.ySym t) := by
    rw [show deriv (fun ξ : ℝ => -(endpointScale t ξ)^2) x =
        -deriv (fun ξ : ℝ => (endpointScale t ξ)^2) x by
          exact (deriv.neg
            (f := fun ξ : ℝ => (endpointScale t ξ)^2) (x := x))]
    rw [endpointScale_sq_x_deriv]
  calc
    deriv (fun ξ : ℝ => Real.exp (-(endpointScale t ξ)^2)) x =
        Real.exp (-(endpointScale t x)^2) *
          deriv (fun ξ : ℝ => -(endpointScale t ξ)^2) x := by
          simpa using (deriv_exp hdiff)
    _ = Real.exp (-(endpointScale t x)^2) *
        (-(2 * endpointScale t x / TimeScaling.ySym t)) := by
          rw [hinner]

/-- NODE HE.ExplicitSolution.endpointRationalFactor_x_deriv
deps: HE.ExplicitSolution.endpointScale_sq_x_deriv
statement: spatial derivative of the rational factor in the even profile.
-/
theorem endpointRationalFactor_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => (1 + (endpointScale t ξ)^2)⁻¹) x =
      -(2 * endpointScale t x / TimeScaling.ySym t) /
        (1 + (endpointScale t x)^2)^2 := by
  have hdiff : DifferentiableAt ℝ
      (fun ξ : ℝ => 1 + (endpointScale t ξ)^2) x := by
    unfold endpointScale
    fun_prop
  have hne : 1 + (endpointScale t x)^2 ≠ 0 := by positivity
  have hinner :
      deriv (fun ξ : ℝ => 1 + (endpointScale t ξ)^2) x =
        2 * endpointScale t x / TimeScaling.ySym t := by
    rw [show deriv (fun ξ : ℝ => 1 + (endpointScale t ξ)^2) x =
        deriv (fun ξ : ℝ => (endpointScale t ξ)^2) x by
          exact (deriv_const_add
            (f := fun ξ : ℝ => (endpointScale t ξ)^2) (x := x) (1 : ℝ))]
    rw [endpointScale_sq_x_deriv]
  rw [deriv_fun_inv'' hdiff hne]
  rw [hinner]

/-- NODE HE.ExplicitSolution.endpointEvenProfile_scale_x_deriv
deps: HE.ExplicitSolution.endpointExpFactor_x_deriv, HE.ExplicitSolution.endpointRationalFactor_x_deriv
statement: spatial derivative of the even profile after inserting `s=x/y(t)`.
-/
theorem endpointEvenProfile_scale_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenProfile (endpointScale t ξ)) x =
      (Real.exp (-(endpointScale t x)^2) *
          (-(2 * endpointScale t x / TimeScaling.ySym t))) *
        (1 + (endpointScale t x)^2)⁻¹ +
      Real.exp (-(endpointScale t x)^2) *
        (-(2 * endpointScale t x / TimeScaling.ySym t) /
          (1 + (endpointScale t x)^2)^2) := by
  unfold endpointEvenProfile
  have hdiffExp : DifferentiableAt ℝ
      (fun ξ : ℝ => Real.exp (-(endpointScale t ξ)^2)) x := by
    unfold endpointScale
    fun_prop
  have hdiffRat : DifferentiableAt ℝ
      (fun ξ : ℝ => (1 + (endpointScale t ξ)^2)⁻¹) x := by
    apply DifferentiableAt.inv
    · unfold endpointScale
      fun_prop
    · positivity
  rw [deriv_fun_mul hdiffExp hdiffRat]
  rw [endpointExpFactor_x_deriv, endpointRationalFactor_x_deriv]

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_profile, HE.ExplicitSolution.endpointEvenProfile_scale_x_deriv
statement: first spatial derivative of the concrete even amplitude.
-/
theorem endpointEvenAmplitude_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        ((Real.exp (-(endpointScale t x)^2) *
            (-(2 * endpointScale t x / TimeScaling.ySym t))) *
          (1 + (endpointScale t x)^2)⁻¹ +
        Real.exp (-(endpointScale t x)^2) *
          (-(2 * endpointScale t x / TimeScaling.ySym t) /
            (1 + (endpointScale t x)^2)^2)) := by
  have hfun : (fun ξ : ℝ => endpointEvenAmplitude t ξ) =
      fun ξ : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym t)) *
          endpointEvenProfile (endpointScale t ξ) := by
    funext ξ
    rw [endpointEvenAmplitude_profile]
  rw [hfun]
  have hdiffProfile : DifferentiableAt ℝ
      (fun ξ : ℝ => endpointEvenProfile (endpointScale t ξ)) x := by
    unfold endpointEvenProfile
    have hdiffExp : DifferentiableAt ℝ
        (fun ξ : ℝ => Real.exp (-(endpointScale t ξ)^2)) x := by
      unfold endpointScale
      fun_prop
    have hdiffRat : DifferentiableAt ℝ
        (fun ξ : ℝ => (1 + (endpointScale t ξ)^2)⁻¹) x := by
      apply DifferentiableAt.inv
      · unfold endpointScale
        fun_prop
      · positivity
    exact hdiffExp.mul hdiffRat
  rw [deriv_const_mul (1 / Real.sqrt (TimeScaling.ySym t)) hdiffProfile]
  rw [endpointEvenProfile_scale_x_deriv]

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_ratio
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_deriv
statement: compact first spatial amplitude derivative `ρ_x = ρ L(s)/y`.
-/
theorem endpointEvenAmplitude_x_deriv_ratio (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x =
      endpointEvenAmplitude t x *
        endpointProfileSlope (endpointScale t x) / TimeScaling.ySym t := by
  rw [endpointEvenAmplitude_x_deriv]
  unfold endpointEvenAmplitude endpointProfileSlope
  set s : ℝ := endpointScale t x
  set y : ℝ := TimeScaling.ySym t
  have hy : y ≠ 0 := by
    dsimp [y]
    exact TimeScaling.symmetric_y_ne_zero t
  have hs : 1 + s^2 ≠ 0 := by positivity
  field_simp [hy, hs]
  ring

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_second_deriv_ratio
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_ratio, HE.ExplicitSolution.endpointEvenProfile_mul_slope_deriv, HE.ExplicitSolution.endpointScale_x_deriv
statement: compact second spatial amplitude derivative `ρ_xx = ρ M(s)/y^2`.
-/
theorem endpointEvenAmplitude_x_second_deriv_ratio (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ)) x =
      endpointEvenAmplitude t x *
        endpointProfileSecondRatio (endpointScale t x) / (TimeScaling.ySym t)^2 := by
  have hfun : deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) =
      fun η : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym t)) *
          (endpointEvenProfile (endpointScale t η) *
            endpointProfileSlope (endpointScale t η)) / TimeScaling.ySym t := by
    funext η
    rw [endpointEvenAmplitude_x_deriv_ratio]
    rw [endpointEvenAmplitude_profile]
    ring
  rw [hfun]
  have hy : TimeScaling.ySym t ≠ 0 := TimeScaling.symmetric_y_ne_zero t
  have hscale : HasDerivAt
      (fun η : ℝ => endpointScale t η) (1 / TimeScaling.ySym t) x := by
    have hdiff : DifferentiableAt ℝ (fun η : ℝ => endpointScale t η) x := by
      unfold endpointScale
      fun_prop
    simpa [endpointScale_x_deriv t x] using hdiff.hasDerivAt
  have hprof : HasDerivAt
      (fun z : ℝ => endpointEvenProfile z * endpointProfileSlope z)
      (endpointEvenProfile (endpointScale t x) *
        endpointProfileSecondRatio (endpointScale t x))
      (endpointScale t x) := by
    have hdiff : DifferentiableAt ℝ
        (fun z : ℝ => endpointEvenProfile z * endpointProfileSlope z)
        (endpointScale t x) := by
      apply DifferentiableAt.mul
      · unfold endpointEvenProfile
        apply DifferentiableAt.mul
        · fun_prop
        · apply DifferentiableAt.inv
          · fun_prop
          · positivity
      · unfold endpointProfileSlope
        apply DifferentiableAt.div
        · fun_prop
        · fun_prop
        · positivity
    simpa [endpointEvenProfile_mul_slope_deriv] using hdiff.hasDerivAt
  have hcomp := hprof.comp x hscale
  have hderiv_comp :
      deriv (fun η : ℝ => endpointEvenProfile (endpointScale t η) *
        endpointProfileSlope (endpointScale t η)) x =
        (endpointEvenProfile (endpointScale t x) *
          endpointProfileSecondRatio (endpointScale t x)) *
          (1 / TimeScaling.ySym t) := by
    simpa [Function.comp_def] using hcomp.deriv
  have hinnerDiff : DifferentiableAt ℝ
      (fun η : ℝ => endpointEvenProfile (endpointScale t η) *
        endpointProfileSlope (endpointScale t η)) x :=
    hcomp.differentiableAt
  rw [deriv_div_const]
  rw [deriv_const_mul]
  · rw [hderiv_comp]
    rw [endpointEvenAmplitude_profile]
    field_simp [hy]
  · exact hinnerDiff

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_differentiableAt
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_deriv
statement: the first spatial derivative of the amplitude is differentiable.
-/
theorem endpointEvenAmplitude_x_deriv_differentiableAt (t x : ℝ) :
    DifferentiableAt ℝ
      (fun η : ℝ => deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η) x := by
  have hfun : (fun η : ℝ => deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η) =
      fun η : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym t)) *
          ((Real.exp (-(endpointScale t η)^2) *
              (-(2 * endpointScale t η / TimeScaling.ySym t))) *
            (1 + (endpointScale t η)^2)⁻¹ +
          Real.exp (-(endpointScale t η)^2) *
            (-(2 * endpointScale t η / TimeScaling.ySym t) /
              (1 + (endpointScale t η)^2)^2)) := by
    funext η
    exact endpointEvenAmplitude_x_deriv t η
  rw [hfun]
  have hExp : DifferentiableAt ℝ
      (fun η : ℝ => Real.exp (-(endpointScale t η)^2)) x := by
    unfold endpointScale
    fun_prop
  have hLin : DifferentiableAt ℝ
      (fun η : ℝ => -(2 * endpointScale t η / TimeScaling.ySym t)) x := by
    unfold endpointScale
    fun_prop
  have hBase : DifferentiableAt ℝ
      (fun η : ℝ => 1 + (endpointScale t η)^2) x := by
    unfold endpointScale
    fun_prop
  have hBase_ne : 1 + (endpointScale t x)^2 ≠ 0 := by positivity
  have hRat : DifferentiableAt ℝ
      (fun η : ℝ => (1 + (endpointScale t η)^2)⁻¹) x :=
    hBase.inv hBase_ne
  have hDen2 : DifferentiableAt ℝ
      (fun η : ℝ => (1 + (endpointScale t η)^2)^2) x :=
    hBase.pow 2
  have hDen2_ne : (1 + (endpointScale t x)^2)^2 ≠ 0 :=
    pow_ne_zero 2 hBase_ne
  have hFrac : DifferentiableAt ℝ
      (fun η : ℝ => -(2 * endpointScale t η / TimeScaling.ySym t) /
        (1 + (endpointScale t η)^2)^2) x :=
    hLin.div hDen2 hDen2_ne
  exact (((hExp.mul hLin).mul hRat).add (hExp.mul hFrac)).const_mul
    (1 / Real.sqrt (TimeScaling.ySym t))

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_differentiableAt_x
deps: HE.ExplicitSolution.endpointEvenAmplitude_profile
statement: the concrete even amplitude is spatially differentiable.
-/
theorem endpointEvenAmplitude_differentiableAt_x (t x : ℝ) :
    DifferentiableAt ℝ (fun ξ : ℝ => endpointEvenAmplitude t ξ) x := by
  have hfun : (fun ξ : ℝ => endpointEvenAmplitude t ξ) =
      fun ξ : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym t)) *
          endpointEvenProfile (endpointScale t ξ) := by
    funext ξ
    rw [endpointEvenAmplitude_profile]
  rw [hfun]
  have hdiffProfile : DifferentiableAt ℝ
      (fun ξ : ℝ => endpointEvenProfile (endpointScale t ξ)) x := by
    unfold endpointEvenProfile
    have hdiffExp : DifferentiableAt ℝ
        (fun ξ : ℝ => Real.exp (-(endpointScale t ξ)^2)) x := by
      unfold endpointScale
      fun_prop
    have hdiffRat : DifferentiableAt ℝ
        (fun ξ : ℝ => (1 + (endpointScale t ξ)^2)⁻¹) x := by
      apply DifferentiableAt.inv
      · unfold endpointScale
        fun_prop
      · positivity
    exact hdiffExp.mul hdiffRat
  exact hdiffProfile.const_mul (1 / Real.sqrt (TimeScaling.ySym t))

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_complex_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_differentiableAt_x
statement: complex-valued spatial derivative of the real amplitude.
-/
theorem endpointEvenAmplitude_x_complex_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => (endpointEvenAmplitude t ξ : ℂ)) x =
      ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x : ℝ) : ℂ) := by
  have hreal := endpointEvenAmplitude_differentiableAt_x t x
  simpa using hreal.hasDerivAt.ofReal_comp.deriv

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_differentiableAt_t
deps: HE.ExplicitSolution.endpointEvenAmplitude_profile, HE.ExplicitSolution.endpointScale_differentiableAt_t, HE.TimeScaling.ySym_hasDerivAt, HE.TimeScaling.symmetric_y_pos
statement: the concrete even amplitude is time differentiable.
-/
theorem endpointEvenAmplitude_differentiableAt_t (t x : ℝ) :
    DifferentiableAt ℝ (fun τ : ℝ => endpointEvenAmplitude τ x) t := by
  have hfun : (fun τ : ℝ => endpointEvenAmplitude τ x) =
      fun τ : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym τ)) *
          endpointEvenProfile (endpointScale τ x) := by
    funext τ
    rw [endpointEvenAmplitude_profile]
  rw [hfun]
  have hdiffSqrt : DifferentiableAt ℝ
      (fun τ : ℝ => Real.sqrt (TimeScaling.ySym τ)) t :=
    (TimeScaling.ySym_hasDerivAt t).differentiableAt.sqrt
      (TimeScaling.symmetric_y_ne_zero t)
  have hsqrt_ne : Real.sqrt (TimeScaling.ySym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos t))
  have hdiffWidth : DifferentiableAt ℝ
      (fun τ : ℝ => 1 / Real.sqrt (TimeScaling.ySym τ)) t :=
    (differentiableAt_const (1 : ℝ)).div hdiffSqrt hsqrt_ne
  have hdiffScale := endpointScale_differentiableAt_t t x
  have hdiffProfile : DifferentiableAt ℝ
      (fun τ : ℝ => endpointEvenProfile (endpointScale τ x)) t := by
    unfold endpointEvenProfile
    have hdiffExp : DifferentiableAt ℝ
        (fun τ : ℝ => Real.exp (-(endpointScale τ x)^2)) t := by
      fun_prop
    have hdiffRat : DifferentiableAt ℝ
        (fun τ : ℝ => (1 + (endpointScale τ x)^2)⁻¹) t := by
      apply DifferentiableAt.inv
      · exact (differentiableAt_const (1 : ℝ)).add (hdiffScale.pow 2)
      · positivity
    exact hdiffExp.mul hdiffRat
  exact hdiffWidth.mul hdiffProfile

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_t_deriv_ratio
deps: HE.ExplicitSolution.endpointEvenAmplitude_profile, HE.ExplicitSolution.endpointWidthFactor_t_deriv, HE.ExplicitSolution.endpointEvenProfile_deriv, HE.ExplicitSolution.endpointScale_t_deriv
statement: compact time amplitude derivative.
-/
theorem endpointEvenAmplitude_t_deriv_ratio (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t =
      endpointEvenAmplitude t x *
        (-(deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t)) -
          endpointScale t x * deriv TimeScaling.ySym t / TimeScaling.ySym t *
            endpointProfileSlope (endpointScale t x)) := by
  have hfun : (fun τ : ℝ => endpointEvenAmplitude τ x) =
      fun τ : ℝ =>
        (1 / Real.sqrt (TimeScaling.ySym τ)) *
          endpointEvenProfile (endpointScale τ x) := by
    funext τ
    rw [endpointEvenAmplitude_profile]
  rw [hfun]
  have hy : TimeScaling.ySym t ≠ 0 := TimeScaling.symmetric_y_ne_zero t
  have hypos : 0 < TimeScaling.ySym t := TimeScaling.symmetric_y_pos t
  have hsqrt_ne : Real.sqrt (TimeScaling.ySym t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hypos)
  have hdiffWidth : DifferentiableAt ℝ
      (fun τ : ℝ => 1 / Real.sqrt (TimeScaling.ySym τ)) t := by
    have hdiffSqrt : DifferentiableAt ℝ
        (fun τ : ℝ => Real.sqrt (TimeScaling.ySym τ)) t :=
      (TimeScaling.ySym_hasDerivAt t).differentiableAt.sqrt hy
    exact (differentiableAt_const (1 : ℝ)).div hdiffSqrt hsqrt_ne
  have hscale : HasDerivAt
      (fun τ : ℝ => endpointScale τ x)
      (-x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2) t := by
    have hdiff := endpointScale_differentiableAt_t t x
    simpa [endpointScale_t_deriv t x] using hdiff.hasDerivAt
  have hprof : HasDerivAt endpointEvenProfile
      (endpointEvenProfile (endpointScale t x) *
        endpointProfileSlope (endpointScale t x))
      (endpointScale t x) := by
    have hdiff : DifferentiableAt ℝ endpointEvenProfile
        (endpointScale t x) := by
      unfold endpointEvenProfile
      apply DifferentiableAt.mul
      · fun_prop
      · apply DifferentiableAt.inv
        · fun_prop
        · positivity
    simpa [endpointEvenProfile_deriv] using hdiff.hasDerivAt
  have hprofileComp := hprof.comp t hscale
  have hprofile_deriv :
      deriv (fun τ : ℝ => endpointEvenProfile (endpointScale τ x)) t =
        (endpointEvenProfile (endpointScale t x) *
          endpointProfileSlope (endpointScale t x)) *
          (-x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2) := by
    simpa [Function.comp_def] using hprofileComp.deriv
  have hdiffProfile : DifferentiableAt ℝ
      (fun τ : ℝ => endpointEvenProfile (endpointScale τ x)) t :=
    hprofileComp.differentiableAt
  rw [deriv_fun_mul hdiffWidth hdiffProfile]
  rw [endpointWidthFactor_t_deriv, hprofile_deriv]
  rw [endpointEvenAmplitude_profile]
  unfold endpointScale
  field_simp [hy, hsqrt_ne]
  ring

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_t_complex_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_differentiableAt_t
statement: complex-valued time derivative of the real amplitude.
-/
theorem endpointEvenAmplitude_t_complex_deriv (t x : ℝ) :
    deriv (fun τ : ℝ => (endpointEvenAmplitude τ x : ℂ)) t =
      ((deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t : ℝ) : ℂ) := by
  have hreal := endpointEvenAmplitude_differentiableAt_t t x
  simpa using hreal.hasDerivAt.ofReal_comp.deriv

/-! ## Complex solution derivatives -/

/-- NODE HE.ExplicitSolution.endpointEvenSolution_x_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_complex_deriv, HE.ExplicitSolution.phaseExp_x_deriv
statement: first spatial derivative of the concrete complex solution.
-/
theorem endpointEvenSolution_x_deriv (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenSolution t ξ) x =
      ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x : ℝ) : ℂ) *
        Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) +
      (endpointEvenAmplitude t x : ℂ) *
        (Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
          (Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x : ℂ))) := by
  unfold endpointEvenSolution
  have hdiffAmpC : DifferentiableAt ℝ
      (fun ξ : ℝ => (endpointEvenAmplitude t ξ : ℂ)) x := by
    exact (endpointEvenAmplitude_differentiableAt_x t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffPhase : DifferentiableAt ℝ
      (fun ξ : ℝ => (endpointEvenPhase t ξ : ℂ)) x := by
    have hreal : DifferentiableAt ℝ (fun ξ : ℝ => endpointEvenPhase t ξ) x := by
      unfold endpointEvenPhase
      fun_prop
    have hderiv : HasDerivAt (fun ξ : ℝ => endpointEvenPhase t ξ)
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) x := by
      simpa [phase_x_deriv t x] using hreal.hasDerivAt
    exact hderiv.ofReal_comp.differentiableAt
  have hdiffInner : DifferentiableAt ℝ
      (fun ξ : ℝ => Complex.I * (endpointEvenPhase t ξ : ℂ)) x :=
    hdiffPhase.const_mul Complex.I
  have hdiffExp : DifferentiableAt ℝ
      (fun ξ : ℝ => Complex.exp (Complex.I * (endpointEvenPhase t ξ : ℂ))) x :=
    hdiffInner.cexp
  rw [deriv_fun_mul hdiffAmpC hdiffExp]
  rw [endpointEvenAmplitude_x_complex_deriv, phaseExp_x_deriv]

/-- NODE HE.ExplicitSolution.endpointEvenSolution_x_deriv_compact
deps: HE.ExplicitSolution.endpointEvenSolution_x_deriv
statement: compact form of the first spatial derivative of the concrete solution.
-/
theorem endpointEvenSolution_x_deriv_compact (t x : ℝ) :
    deriv (fun ξ : ℝ => endpointEvenSolution t ξ) x =
      endpointEvenSolutionX t x := by
  rw [endpointEvenSolution_x_deriv]
  rfl

/-- NODE HE.ExplicitSolution.endpointEvenSolution_x_deriv_differentiableAt
deps: HE.ExplicitSolution.endpointEvenSolution_x_deriv, HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_differentiableAt
statement: the first spatial derivative of the complex solution is differentiable.
-/
theorem endpointEvenSolution_x_deriv_differentiableAt (t x : ℝ) :
    DifferentiableAt ℝ
      (fun η : ℝ => deriv (fun ξ : ℝ => endpointEvenSolution t ξ) η) x := by
  have hfun : (fun η : ℝ => deriv (fun ξ : ℝ => endpointEvenSolution t ξ) η) =
      fun η : ℝ =>
        ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η : ℝ) : ℂ) *
          Complex.exp (Complex.I * (endpointEvenPhase t η : ℂ)) +
        (endpointEvenAmplitude t η : ℂ) *
          (Complex.exp (Complex.I * (endpointEvenPhase t η : ℂ)) *
            (Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * η : ℂ))) := by
    funext η
    exact endpointEvenSolution_x_deriv t η
  rw [hfun]
  have hdiffAmpDerivC : DifferentiableAt ℝ
      (fun η : ℝ =>
        ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η : ℝ) : ℂ)) x :=
    (endpointEvenAmplitude_x_deriv_differentiableAt t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffPhase : DifferentiableAt ℝ
      (fun η : ℝ => (endpointEvenPhase t η : ℂ)) x := by
    have hreal : DifferentiableAt ℝ (fun η : ℝ => endpointEvenPhase t η) x := by
      unfold endpointEvenPhase
      fun_prop
    have hderiv : HasDerivAt (fun η : ℝ => endpointEvenPhase t η)
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) x := by
      simpa [phase_x_deriv t x] using hreal.hasDerivAt
    exact hderiv.ofReal_comp.differentiableAt
  have hdiffInner : DifferentiableAt ℝ
      (fun η : ℝ => Complex.I * (endpointEvenPhase t η : ℂ)) x :=
    hdiffPhase.const_mul Complex.I
  have hdiffExp : DifferentiableAt ℝ
      (fun η : ℝ => Complex.exp (Complex.I * (endpointEvenPhase t η : ℂ))) x :=
    hdiffInner.cexp
  have hdiffAmpC : DifferentiableAt ℝ
      (fun η : ℝ => (endpointEvenAmplitude t η : ℂ)) x :=
    (endpointEvenAmplitude_differentiableAt_x t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffPhaseX : DifferentiableAt ℝ
      (fun η : ℝ =>
        Complex.I * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * η : ℂ)) x := by
    have hreal : DifferentiableAt ℝ
        (fun η : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * η) x := by
      fun_prop
    simpa using
      hreal.hasDerivAt.ofReal_comp.differentiableAt.const_mul Complex.I
  exact (hdiffAmpDerivC.mul hdiffExp).add
    (hdiffAmpC.mul (hdiffExp.mul hdiffPhaseX))

/-- NODE HE.ExplicitSolution.endpointEvenAmplitude_x_second_complex_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_differentiableAt
statement: complex-valued derivative of the first spatial amplitude derivative.
-/
theorem endpointEvenAmplitude_x_second_complex_deriv (t x : ℝ) :
    deriv
      (fun η : ℝ =>
        ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η : ℝ) : ℂ)) x =
      ((deriv (deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ)) x : ℝ) : ℂ) := by
  have hreal := endpointEvenAmplitude_x_deriv_differentiableAt t x
  simpa using hreal.hasDerivAt.ofReal_comp.deriv

/-- NODE HE.ExplicitSolution.endpointEvenSolutionX_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_second_complex_deriv, HE.ExplicitSolution.endpointPhaseFactor_x_deriv, HE.ExplicitSolution.endpointEvenAmplitude_x_complex_deriv, HE.ExplicitSolution.endpointPhaseFactor_mul_xFactor_x_deriv
statement: derivative of the compact first spatial derivative is the compact second spatial derivative.
-/
theorem endpointEvenSolutionX_deriv (t x : ℝ) :
    deriv (fun η : ℝ => endpointEvenSolutionX t η) x =
      endpointEvenSolutionXX t x := by
  unfold endpointEvenSolutionX endpointEvenSolutionXX
  have hdiffAmpDerivC : DifferentiableAt ℝ
      (fun η : ℝ =>
        ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η : ℝ) : ℂ)) x :=
    (endpointEvenAmplitude_x_deriv_differentiableAt t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffPhase : DifferentiableAt ℝ
      (fun η : ℝ => endpointPhaseFactor t η) x := by
    unfold endpointPhaseFactor
    have hreal : DifferentiableAt ℝ (fun η : ℝ => endpointEvenPhase t η) x := by
      unfold endpointEvenPhase
      fun_prop
    have hcomplex : DifferentiableAt ℝ
        (fun η : ℝ => (endpointEvenPhase t η : ℂ)) x :=
      hreal.hasDerivAt.ofReal_comp.differentiableAt
    exact (hcomplex.const_mul Complex.I).cexp
  have hdiffAmpC : DifferentiableAt ℝ
      (fun η : ℝ => (endpointEvenAmplitude t η : ℂ)) x :=
    (endpointEvenAmplitude_differentiableAt_x t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffX : DifferentiableAt ℝ
      (fun η : ℝ => endpointPhaseXFactor t η) x := by
    unfold endpointPhaseXFactor
    have hreal : DifferentiableAt ℝ
        (fun η : ℝ => ((2 * t - 1) / (2 * TimeScaling.qSym t)) * η) x := by
      fun_prop
    have hcomplex : DifferentiableAt ℝ
        (fun η : ℝ => (((2 * t - 1) / (2 * TimeScaling.qSym t)) * η : ℂ)) x := by
      simpa using hreal.hasDerivAt.ofReal_comp.differentiableAt
    exact hcomplex.const_mul Complex.I
  have hdiffPhaseX : DifferentiableAt ℝ
      (fun η : ℝ => endpointPhaseFactor t η * endpointPhaseXFactor t η) x :=
    hdiffPhase.mul hdiffX
  have hdiffLeft : DifferentiableAt ℝ
      (fun η : ℝ =>
        ((deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) η : ℝ) : ℂ) *
          endpointPhaseFactor t η) x :=
    hdiffAmpDerivC.mul hdiffPhase
  have hdiffRight : DifferentiableAt ℝ
      (fun η : ℝ =>
        (endpointEvenAmplitude t η : ℂ) *
          (endpointPhaseFactor t η * endpointPhaseXFactor t η)) x :=
    hdiffAmpC.mul hdiffPhaseX
  rw [deriv_fun_add hdiffLeft hdiffRight]
  rw [deriv_fun_mul hdiffAmpDerivC hdiffPhase]
  rw [deriv_fun_mul hdiffAmpC hdiffPhaseX]
  rw [endpointEvenAmplitude_x_second_complex_deriv]
  rw [endpointPhaseFactor_x_deriv]
  rw [endpointEvenAmplitude_x_complex_deriv]
  rw [endpointPhaseFactor_mul_xFactor_x_deriv]
  ring

/-- NODE HE.ExplicitSolution.endpointEvenSolution_x_second_deriv_reduce
deps: HE.ExplicitSolution.endpointEvenSolution_x_deriv_compact
statement: the second spatial derivative is the derivative of the compact `u_x` formula.
-/
theorem endpointEvenSolution_x_second_deriv_reduce (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointEvenSolution t ξ)) x =
      deriv (fun η : ℝ => endpointEvenSolutionX t η) x := by
  have hfun : deriv (fun ξ : ℝ => endpointEvenSolution t ξ) =
      fun η : ℝ => endpointEvenSolutionX t η := by
    funext η
    exact endpointEvenSolution_x_deriv_compact t η
  rw [hfun]

/-- NODE HE.ExplicitSolution.endpointEvenSolution_x_second_deriv_compact
deps: HE.ExplicitSolution.endpointEvenSolution_x_second_deriv_reduce, HE.ExplicitSolution.endpointEvenSolutionX_deriv
statement: compact form of the second spatial derivative of the concrete solution.
-/
theorem endpointEvenSolution_x_second_deriv_compact (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointEvenSolution t ξ)) x =
      endpointEvenSolutionXX t x := by
  rw [endpointEvenSolution_x_second_deriv_reduce]
  rw [endpointEvenSolutionX_deriv]

/-- NODE HE.ExplicitSolution.endpointEvenSolution_t_deriv
deps: HE.ExplicitSolution.endpointEvenAmplitude_t_complex_deriv, HE.ExplicitSolution.phaseExp_t_deriv
statement: first time derivative of the concrete complex solution.
-/
theorem endpointEvenSolution_t_deriv (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenSolution τ x) t =
      ((deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t : ℝ) : ℂ) *
        Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) +
      (endpointEvenAmplitude t x : ℂ) *
        (Complex.exp (Complex.I * (endpointEvenPhase t x : ℂ)) *
          (Complex.I *
            (((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
              3 / (2 * TimeScaling.qSym t) : ℝ) : ℂ))) := by
  unfold endpointEvenSolution
  have hdiffAmpC : DifferentiableAt ℝ
      (fun τ : ℝ => (endpointEvenAmplitude τ x : ℂ)) t := by
    exact (endpointEvenAmplitude_differentiableAt_t t x).hasDerivAt.ofReal_comp.differentiableAt
  have hdiffPhase : DifferentiableAt ℝ
      (fun τ : ℝ => (endpointEvenPhase τ x : ℂ)) t := by
    have hreal : DifferentiableAt ℝ (fun τ : ℝ => endpointEvenPhase τ x) t := by
      unfold endpointEvenPhase
      exact ((endpointB_differentiableAt t).mul (differentiableAt_const _)).add
        (((show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
          fun_prop).arctan).const_mul (3 / 2))
    have hderiv : HasDerivAt (fun τ : ℝ => endpointEvenPhase τ x)
        ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          3 / (2 * TimeScaling.qSym t)) t := by
      simpa [phase_t_deriv t x] using hreal.hasDerivAt
    exact hderiv.ofReal_comp.differentiableAt
  have hdiffInner : DifferentiableAt ℝ
      (fun τ : ℝ => Complex.I * (endpointEvenPhase τ x : ℂ)) t :=
    hdiffPhase.const_mul Complex.I
  have hdiffExp : DifferentiableAt ℝ
      (fun τ : ℝ => Complex.exp (Complex.I * (endpointEvenPhase τ x : ℂ))) t :=
    hdiffInner.cexp
  rw [deriv_fun_mul hdiffAmpC hdiffExp]
  rw [endpointEvenAmplitude_t_complex_deriv, phaseExp_t_deriv]

/-- NODE HE.ExplicitSolution.endpointEvenSolution_t_deriv_compact
deps: HE.ExplicitSolution.endpointEvenSolution_t_deriv
statement: compact form of the first time derivative of the concrete solution.
-/
theorem endpointEvenSolution_t_deriv_compact (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenSolution τ x) t =
      endpointEvenSolutionT t x := by
  rw [endpointEvenSolution_t_deriv]
  rfl

/-! ## Schrödinger residual and real-imaginary cancellation -/

/-- NODE HE.ExplicitSolution.schrodingerResidual_derivative_reduction
deps: HE.ExplicitSolution.endpointEvenSolution_t_deriv_compact, HE.ExplicitSolution.endpointEvenSolution_x_second_deriv_reduce
statement: the Schrödinger residual reduces to the compact derivative formulas for `u_t` and `u_x`.
-/
theorem schrodingerResidual_derivative_reduction (t x : ℝ) :
    schrodingerResidual t x =
      Complex.I * endpointEvenSolutionT t x +
        deriv (fun η : ℝ => endpointEvenSolutionX t η) x -
          (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x := by
  unfold schrodingerResidual
  rw [endpointEvenSolution_t_deriv_compact]
  rw [endpointEvenSolution_x_second_deriv_reduce]

/-- NODE HE.ExplicitSolution.schrodingerResidual_compact
deps: HE.ExplicitSolution.endpointEvenSolution_t_deriv_compact, HE.ExplicitSolution.endpointEvenSolution_x_second_deriv_compact
statement: the Schrödinger residual in the fully compact `T/XX` form.
-/
theorem schrodingerResidual_compact (t x : ℝ) :
    schrodingerResidual t x =
      Complex.I * endpointEvenSolutionT t x +
        endpointEvenSolutionXX t x -
          (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x := by
  unfold schrodingerResidual
  rw [endpointEvenSolution_t_deriv_compact]
  rw [endpointEvenSolution_x_second_deriv_compact]

/-- NODE HE.ExplicitSolution.compact_residual_decomposition
deps:
statement: compact complex residual split into real and imaginary scalar brackets.
-/
theorem compact_residual_decomposition (t x : ℝ) :
    Complex.I * endpointEvenSolutionT t x + endpointEvenSolutionXX t x -
      (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x =
    endpointPhaseFactor t x *
      (((deriv (deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ)) x -
        endpointEvenAmplitude t x *
          ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
            3 / (2 * TimeScaling.qSym t)) -
        endpointEvenAmplitude t x *
          (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 -
        endpointEvenPotential t x * endpointEvenAmplitude t x : ℝ) : ℂ) +
      Complex.I *
        ((deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t +
          2 * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) *
            deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x +
          ((2 * t - 1) / (2 * TimeScaling.qSym t)) *
            endpointEvenAmplitude t x : ℝ) : ℂ)) := by
  unfold endpointEvenSolutionT endpointEvenSolutionXX endpointEvenSolution endpointPhaseFactor
    endpointPhaseTFactor endpointPhaseXFactor endpointPhaseXXFactor
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- NODE HE.ExplicitSolution.compact_residual_implies_schrodinger
deps: HE.ExplicitSolution.schrodingerResidual_compact
statement: the compact residual identity implies the concrete Schrödinger equation.
-/
theorem compact_residual_implies_schrodinger
    (hcompact :
      ∀ t x : ℝ,
        Complex.I * endpointEvenSolutionT t x +
          endpointEvenSolutionXX t x -
            (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x = 0) :
    FullSchrodingerEquation := by
  intro t x
  rw [schrodingerResidual_compact]
  exact hcompact t x

/-- NODE HE.ExplicitSolution.endpointEvenPotential_width_form
deps: HE.TimeScaling.symmetric_y_sq, HE.TimeScaling.symmetric_q_ne_zero
statement: the concrete potential in width variables.
-/
theorem endpointEvenPotential_width_form (t x : ℝ) :
    endpointEvenPotential t x =
      -2 * ((endpointScale t x)^2 + 5) /
        ((TimeScaling.ySym t)^2 * (1 + (endpointScale t x)^2)^2) := by
  unfold endpointEvenPotential
  have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
  have hy_sq : (TimeScaling.ySym t)^2 =
      4 * TimeScaling.qSym t := TimeScaling.symmetric_y_sq t
  rw [hy_sq]
  field_simp [hq]
  ring

/-- NODE HE.ExplicitSolution.amplitude_transport_identity
deps: HE.ExplicitSolution.endpointEvenAmplitude_t_deriv_ratio, HE.ExplicitSolution.endpointEvenAmplitude_x_deriv_ratio
statement: real transport identity cancelling the imaginary part of the residual.
-/
theorem amplitude_transport_identity (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t +
      2 * (endpointScale t x * deriv TimeScaling.ySym t / 2) *
        deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x +
      (deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t)) *
        endpointEvenAmplitude t x = 0 := by
  rw [endpointEvenAmplitude_t_deriv_ratio]
  rw [endpointEvenAmplitude_x_deriv_ratio]
  unfold endpointProfileSlope endpointScale
  set y : ℝ := TimeScaling.ySym t
  have hy : y ≠ 0 := by
    dsimp [y]
    exact TimeScaling.symmetric_y_ne_zero t
  have hden : 1 + (x / y)^2 ≠ 0 := by positivity
  field_simp [hy, hden]
  ring

/-- NODE HE.ExplicitSolution.amplitude_transport_q_identity
deps: HE.ExplicitSolution.amplitude_transport_identity, HE.ExplicitSolution.phase_x_width_form, HE.ExplicitSolution.phase_xx_width_form
statement: transport identity in the original `q` phase variables.
-/
theorem amplitude_transport_q_identity (t x : ℝ) :
    deriv (fun τ : ℝ => endpointEvenAmplitude τ x) t +
      2 * (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x) *
        deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ) x +
      ((2 * t - 1) / (2 * TimeScaling.qSym t)) *
        endpointEvenAmplitude t x = 0 := by
  have h := amplitude_transport_identity t x
  rw [← phase_x_width_form t x, ← phase_xx_width_form t] at h
  exact h

/-- NODE HE.ExplicitSolution.amplitude_real_identity
deps: HE.ExplicitSolution.endpointEvenAmplitude_x_second_deriv_ratio, HE.ExplicitSolution.phase_energy_width_identity, HE.ExplicitSolution.endpointEvenPotential_width_form, HE.ExplicitSolution.endpointProfile_real_identity
statement: real amplitude-potential identity cancelling the real part of the residual.
-/
theorem amplitude_real_identity (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => endpointEvenAmplitude t ξ)) x -
      endpointEvenAmplitude t x *
        ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          3 / (2 * TimeScaling.qSym t)) -
      endpointEvenAmplitude t x *
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 -
  endpointEvenPotential t x * endpointEvenAmplitude t x = 0 := by
  rw [endpointEvenAmplitude_x_second_deriv_ratio]
  have hphase := phase_energy_width_identity t x
  have hphase' :
      ((t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          3 / (2 * TimeScaling.qSym t)) =
        (4 * (endpointScale t x)^2 + 6) / (TimeScaling.ySym t)^2 -
          (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 := by
    linarith [hphase]
  rw [hphase']
  rw [endpointEvenPotential_width_form]
  set s : ℝ := endpointScale t x
  set y : ℝ := TimeScaling.ySym t
  have hy : y ≠ 0 := by
    dsimp [y]
    exact TimeScaling.symmetric_y_ne_zero t
  have hden : 1 + s^2 ≠ 0 := by positivity
  have hden2 : (1 + s^2)^2 ≠ 0 := pow_ne_zero 2 hden
  have hprofile :
      endpointProfileSecondRatio s =
        4 * s^2 + 6 - 2 * (s^2 + 5) / (1 + s^2)^2 := by
    have h := endpointProfile_real_identity s
    linarith
  rw [show endpointProfileSecondRatio (endpointScale t x) =
      4 * s^2 + 6 - 2 * (s^2 + 5) / (1 + s^2)^2 by
        simpa [s] using hprofile]
  dsimp [s, y]
  field_simp [hy, hden, hden2]
  ring

/-- NODE HE.ExplicitSolution.compact_residual_identity
deps: HE.ExplicitSolution.compact_residual_decomposition, HE.ExplicitSolution.amplitude_real_identity, HE.ExplicitSolution.amplitude_transport_q_identity
statement: the compact complex residual vanishes.
-/
theorem compact_residual_identity (t x : ℝ) :
    Complex.I * endpointEvenSolutionT t x + endpointEvenSolutionXX t x -
      (endpointEvenPotential t x : ℂ) * endpointEvenSolution t x = 0 := by
  rw [compact_residual_decomposition]
  rw [amplitude_real_identity, amplitude_transport_q_identity]
  simp

/-! ## Critical Gaussian endpoint integrability -/

/-- NODE HE.ExplicitSolution.weighted_amplitude_zero
deps:
statement: at `t=0`, the endpoint Gaussian exactly cancels the exponential part of the amplitude.
-/
theorem weighted_amplitude_zero (x : ℝ) :
    Real.exp (x^2 / 4) * endpointEvenAmplitude 0 x =
      (1 / Real.sqrt 2) * (1 + (x / 2)^2)⁻¹ := by
  unfold endpointEvenAmplitude endpointScale
  rw [show TimeScaling.ySym 0 = 2 by
    unfold TimeScaling.ySym TimeScaling.qSym
    norm_num]
  have hexp : Real.exp (x ^ 2 / 4) * Real.exp (-(x / 2) ^ 2) = 1 := by
    rw [← Real.exp_add]
    have hpow : (x / 2)^2 = x^2 / 4 := by ring
    rw [hpow]
    ring_nf
    norm_num
  calc
    Real.exp (x^2 / 4) *
          ((1 / Real.sqrt 2) * Real.exp (-(x / 2)^2) * (1 + (x / 2)^2)⁻¹)
        = (1 / Real.sqrt 2) *
            (Real.exp (x^2 / 4) * Real.exp (-(x / 2)^2)) *
              (1 + (x / 2)^2)⁻¹ := by
          ring
    _ = (1 / Real.sqrt 2) * (1 + (x / 2)^2)⁻¹ := by
          rw [hexp]
          ring

/-- NODE HE.ExplicitSolution.weighted_amplitude_one
deps:
statement: at `t=1`, the endpoint Gaussian exactly cancels the exponential part of the amplitude.
-/
theorem weighted_amplitude_one (x : ℝ) :
    Real.exp (x^2 / 4) * endpointEvenAmplitude 1 x =
      (1 / Real.sqrt 2) * (1 + (x / 2)^2)⁻¹ := by
  unfold endpointEvenAmplitude endpointScale
  rw [show TimeScaling.ySym 1 = 2 by
    unfold TimeScaling.ySym TimeScaling.qSym
    norm_num]
  have hexp : Real.exp (x ^ 2 / 4) * Real.exp (-(x / 2) ^ 2) = 1 := by
    rw [← Real.exp_add]
    have hpow : (x / 2)^2 = x^2 / 4 := by ring
    rw [hpow]
    ring_nf
    norm_num
  calc
    Real.exp (x^2 / 4) *
          ((1 / Real.sqrt 2) * Real.exp (-(x / 2)^2) * (1 + (x / 2)^2)⁻¹)
        = (1 / Real.sqrt 2) *
            (Real.exp (x^2 / 4) * Real.exp (-(x / 2)^2)) *
              (1 + (x / 2)^2)⁻¹ := by
          ring
    _ = (1 / Real.sqrt 2) * (1 + (x / 2)^2)⁻¹ := by
          rw [hexp]
          ring

/-- NODE HE.ExplicitSolution.sqrt_two_inv_sq
deps:
statement: `(1/sqrt 2)^2 = 1/2`.
-/
theorem sqrt_two_inv_sq : (1 / Real.sqrt 2 : ℝ)^2 = (1 / 2 : ℝ) := by
  have hsqrt : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  calc
    (1 / Real.sqrt 2 : ℝ)^2 = 1 / (Real.sqrt 2)^2 := by ring
    _ = (1 / 2 : ℝ) := by rw [hsqrt]

/-- NODE HE.ExplicitSolution.weighted_amplitude_zero_sq
deps: HE.ExplicitSolution.weighted_amplitude_zero, HE.ExplicitSolution.sqrt_two_inv_sq
statement: squared endpoint profile at `t=0` has the rational tail `(1+(x/2)^2)^{-2}`.
-/
theorem weighted_amplitude_zero_sq (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 0 x)^2 =
      (1 / 2 : ℝ) * ((1 + (x / 2)^2)⁻¹)^2 := by
  rw [weighted_amplitude_zero]
  rw [mul_pow]
  rw [sqrt_two_inv_sq]

/-- NODE HE.ExplicitSolution.weighted_amplitude_one_sq
deps: HE.ExplicitSolution.weighted_amplitude_one, HE.ExplicitSolution.sqrt_two_inv_sq
statement: squared endpoint profile at `t=1` has the same rational tail.
-/
theorem weighted_amplitude_one_sq (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 1 x)^2 =
      (1 / 2 : ℝ) * ((1 + (x / 2)^2)⁻¹)^2 := by
  rw [weighted_amplitude_one]
  rw [mul_pow]
  rw [sqrt_two_inv_sq]

/-- NODE HE.ExplicitSolution.weighted_tail_standard
deps:
statement: the rational endpoint square equals `8/(4+x^2)^2`.
-/
theorem weighted_tail_standard (x : ℝ) :
    (1 / 2 : ℝ) * ((1 + (x / 2)^2)⁻¹)^2 = 8 / (4 + x^2)^2 := by
  have hden : 1 + (x / 2)^2 ≠ 0 := by positivity
  have hden2 : 4 + x^2 ≠ 0 := by positivity
  field_simp [hden, hden2]
  ring

/-- NODE HE.ExplicitSolution.weighted_tail_bound
deps: HE.ExplicitSolution.weighted_tail_standard
statement: the endpoint square is dominated by the standard integrable tail `8/(1+x^2)^2`.
-/
theorem weighted_tail_bound (x : ℝ) :
    (1 / 2 : ℝ) * ((1 + (x / 2)^2)⁻¹)^2 ≤ 8 / (1 + x^2)^2 := by
  rw [weighted_tail_standard]
  have hpos1 : 0 < (1 + x^2)^2 := by positivity
  apply div_le_div_of_nonneg_left
  · norm_num
  · positivity
  · nlinarith [sq_nonneg x]

/-- NODE HE.ExplicitSolution.weighted_amplitude_zero_tail_bound
deps: HE.ExplicitSolution.weighted_amplitude_zero_sq, HE.ExplicitSolution.weighted_tail_bound
statement: the `t=0` weighted square is dominated by `8/(1+x^2)^2`.
-/
theorem weighted_amplitude_zero_tail_bound (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 0 x)^2 ≤ 8 / (1 + x^2)^2 := by
  rw [weighted_amplitude_zero_sq]
  exact weighted_tail_bound x

/-- NODE HE.ExplicitSolution.weighted_amplitude_one_tail_bound
deps: HE.ExplicitSolution.weighted_amplitude_one_sq, HE.ExplicitSolution.weighted_tail_bound
statement: the `t=1` weighted square is dominated by `8/(1+x^2)^2`.
-/
theorem weighted_amplitude_one_tail_bound (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 1 x)^2 ≤ 8 / (1 + x^2)^2 := by
  rw [weighted_amplitude_one_sq]
  exact weighted_tail_bound x

/-- NODE HE.ExplicitSolution.standard_tail_integrable
deps:
statement: the standard controlling tail `8/(1+x^2)` is integrable on the real line.
-/
theorem standard_tail_integrable :
    MeasureTheory.Integrable (fun x : ℝ => 8 / (1 + x^2)) := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (integrable_inv_one_add_sq.const_mul (8 : ℝ))

/-- NODE HE.ExplicitSolution.square_tail_le_standard_tail
deps:
statement: `8/(1+x^2)^2` is bounded above by `8/(1+x^2)`.
-/
theorem square_tail_le_standard_tail (x : ℝ) :
    8 / (1 + x^2)^2 ≤ 8 / (1 + x^2) := by
  have hpos : 0 < 1 + x^2 := by positivity
  apply div_le_div_of_nonneg_left
  · norm_num
  · exact hpos
  · nlinarith [sq_nonneg x]

/-- NODE HE.ExplicitSolution.weighted_amplitude_zero_standard_bound
deps: HE.ExplicitSolution.weighted_amplitude_zero_tail_bound, HE.ExplicitSolution.square_tail_le_standard_tail
statement: the `t=0` weighted square is bounded by the standard integrable tail.
-/
theorem weighted_amplitude_zero_standard_bound (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 0 x)^2 ≤ 8 / (1 + x^2) := by
  exact le_trans (weighted_amplitude_zero_tail_bound x) (square_tail_le_standard_tail x)

/-- NODE HE.ExplicitSolution.weighted_amplitude_one_standard_bound
deps: HE.ExplicitSolution.weighted_amplitude_one_tail_bound, HE.ExplicitSolution.square_tail_le_standard_tail
statement: the `t=1` weighted square is bounded by the standard integrable tail.
-/
theorem weighted_amplitude_one_standard_bound (x : ℝ) :
    (Real.exp (x^2 / 4) * endpointEvenAmplitude 1 x)^2 ≤ 8 / (1 + x^2) := by
  exact le_trans (weighted_amplitude_one_tail_bound x) (square_tail_le_standard_tail x)

/-! ## Final theorem assembly -/

/-- NODE HE.ExplicitSolution.solution_definition
deps: HE.ExplicitSolution.endpoint_solution_nonzero, HE.TimeScaling.ySym_ode
statement: concrete endpoint solution `u` is defined and nontrivial.
-/
theorem solution_definition : ConcreteSolutionDefined := by
  exact ⟨endpoint_solution_nonzero, TimeScaling.ySym_ode⟩

/-- NODE HE.ExplicitSolution.potential_definition
deps: HE.ExplicitSolution.even_potential_bound
statement: concrete real scalar potential `V` is defined and bounded.
-/
theorem potential_definition : ConcretePotentialDefined := by
  exact even_potential_bound

/-- NODE HE.ExplicitSolution.schrodinger_equation
deps: HE.ExplicitSolution.solution_definition, HE.ExplicitSolution.potential_definition, HE.ResidualIdentity.even_residual, HE.ResidualIdentity.odd_residual, HE.ExplicitSolution.compact_residual_implies_schrodinger
statement: the concrete `u,V` satisfy `i∂_t u + Δu = V u`.
-/
theorem schrodinger_equation : FullSchrodingerEquation := by
  have hsolution : ConcreteSolutionDefined := solution_definition
  have hpotential : ConcretePotentialDefined := potential_definition
  have heven := ResidualIdentity.even_residual
  have hodd := ResidualIdentity.odd_residual
  apply compact_residual_implies_schrodinger
  intro t x
  exact compact_residual_identity t x

/-- NODE HE.ExplicitSolution.endpoint_gaussian_L2
deps: HE.ExplicitSolution.solution_definition, HE.DecayEstimates.endpoint_L2, HE.ExplicitSolution.weighted_amplitude_zero_standard_bound, HE.ExplicitSolution.weighted_amplitude_one_standard_bound, HE.ExplicitSolution.standard_tail_integrable
statement: the concrete solution satisfies the endpoint Gaussian weighted `L^2` bounds.
-/
theorem endpoint_gaussian_L2 : FullEndpointGaussianL2 := by
  have hsolution : ConcreteSolutionDefined := solution_definition
  have hproxy := DecayEstimates.endpoint_L2
  exact
    { zero_weighted_square_bound := weighted_amplitude_zero_standard_bound
      one_weighted_square_bound := weighted_amplitude_one_standard_bound
      controlling_tail_integrable := standard_tail_integrable }

/-- NODE HE.ExplicitSolution.real_scalar_endpoint
deps: HE.IntermediateResults.real_scalar_endpoint, HE.ExplicitSolution.schrodinger_equation, HE.ExplicitSolution.endpoint_gaussian_L2
statement: fully semantic real scalar Hardy endpoint example.
-/
theorem real_scalar_endpoint : FullRealScalarEndpoint := by
  have hmain := IntermediateResults.real_scalar_endpoint
  have hpde := schrodinger_equation
  have hl2 := endpoint_gaussian_L2
  exact
    { solution_defined := solution_definition
      potential_defined := potential_definition
      schrodinger_equation := hpde
      endpoint_gaussian_L2 := hl2
      algebraic_claim := hmain }

end ExplicitSolution
end HardyCompactSupport



