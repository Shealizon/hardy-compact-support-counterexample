import Mathlib

/-!
# Gaussian tail exterior profile
-/

noncomputable section

namespace HardyCompactSupport
namespace CompactSupportConstruction

open intervalIntegral
open Filter
open scoped ContDiff

/-! ## Gaussian tail and the exterior profile -/

/-- The Gaussian kernel used in the exterior profile. -/
def gaussianKernel (x : ℝ) : ℝ := Real.exp (-2 * x^2)

/-- A finite-interval primitive of the Gaussian kernel. -/
def gaussianPrimitive (x : ℝ) : ℝ :=
  ∫ s : ℝ in 0..x, gaussianKernel s

/-- The distinguished half-Gaussian mass selecting the decaying exterior mode. -/
def gaussianHalfMass : ℝ :=
  ∫ s : ℝ in Set.Ioi (0 : ℝ), gaussianKernel s

/-- The exterior profile before choosing the decaying integration constant. -/
def exteriorProfile (C x : ℝ) : ℝ :=
  Real.exp (2 * x^2) * (C - gaussianPrimitive x)

lemma gaussianKernel_continuous : Continuous gaussianKernel := by
  unfold gaussianKernel
  fun_prop

/-- NODE HE.CompactSupportConstruction.gaussian_kernel_integrable
deps:
statement: the Gaussian kernel is integrable on the real line.
-/
lemma gaussianKernel_integrable : MeasureTheory.Integrable gaussianKernel := by
  unfold gaussianKernel
  simpa only using integrable_exp_neg_mul_sq (b := (2 : ℝ)) (by norm_num)

/-- NODE HE.CompactSupportConstruction.gaussian_half_mass_tail_identity
deps: HE.CompactSupportConstruction.gaussian_kernel_integrable
statement: subtracting the finite primitive from the half mass gives the positive-side Gaussian tail.
-/
lemma gaussianHalfMass_sub_primitive {x : ℝ} (hx : 0 ≤ x) :
    gaussianHalfMass - gaussianPrimitive x =
      ∫ s : ℝ in Set.Ioi x, gaussianKernel s := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    gaussianKernel_integrable.integrableOn hx
  unfold gaussianHalfMass gaussianPrimitive
  linarith

/-- NODE HE.CompactSupportConstruction.gaussian_tail_positive
deps: HE.CompactSupportConstruction.gaussian_kernel_integrable
statement: every positive-side Gaussian tail has strictly positive mass.
-/
lemma gaussianTail_pos (x : ℝ) :
    0 < ∫ s : ℝ in Set.Ioi x, gaussianKernel s := by
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)
    gaussianKernel_integrable.integrableOn).2
  simp [gaussianKernel, Function.support, (Real.exp_pos _).ne']

/-- NODE HE.CompactSupportConstruction.gaussian_kernel_tends_to_zero
deps:
statement: the Gaussian kernel tends to zero at positive infinity.
-/
lemma gaussianKernel_tendsto_zero :
    Tendsto gaussianKernel atTop (nhds 0) := by
  unfold gaussianKernel
  exact (exp_neg_mul_sq_isLittleO_exp_neg (b := (2 : ℝ)) (by norm_num)).tendsto_zero_of_tendsto
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

/-- NODE HE.CompactSupportConstruction.gaussian_first_moment_tail
deps: HE.CompactSupportConstruction.gaussian_kernel_tends_to_zero
statement: compute the first moment of the Gaussian on a positive half-line.
-/
lemma gaussianFirstMoment_tail (x : ℝ) :
    ∫ s : ℝ in Set.Ioi x, s * gaussianKernel s = gaussianKernel x / 4 := by
  have hderiv : ∀ y ∈ Set.Ici x,
      HasDerivAt (fun z : ℝ => -(1 / 4 : ℝ) * gaussianKernel z)
        (y * gaussianKernel y) y := by
    intro y _
    have hkernel : HasDerivAt gaussianKernel (-4 * y * gaussianKernel y) y := by
      unfold gaussianKernel
      have hinnerRaw :=
        ((hasDerivAt_id y).mul (hasDerivAt_id y)).const_mul (-2)
      have hinner : HasDerivAt (fun z : ℝ => -2 * (z * z))
          (-2 * (y + y)) y := by
        simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using hinnerRaw
      have h := (Real.hasDerivAt_exp (-2 * (y * y))).comp y hinner
      convert h using 1 <;>
        first | rfl | (funext z; simp [Function.comp_def, pow_two]) | ring
    have h := hkernel.const_mul (-(1 / 4 : ℝ))
    convert h using 1 <;> first | rfl | ring
  have hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => s * gaussianKernel s) (Set.Ioi x) := by
    have h := integrable_mul_exp_neg_mul_sq (b := (2 : ℝ)) (by norm_num)
    simpa only [gaussianKernel] using h.integrableOn
  have htend : Tendsto (fun z : ℝ => -(1 / 4 : ℝ) * gaussianKernel z)
      atTop (nhds 0) := by
    simpa using gaussianKernel_tendsto_zero.const_mul (-(1 / 4 : ℝ))
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint htend
  convert h using 1 <;> ring

/-- NODE HE.CompactSupportConstruction.gaussian_tail_mills_bound
deps: HE.CompactSupportConstruction.gaussian_kernel_integrable, HE.CompactSupportConstruction.gaussian_first_moment_tail
statement: bound the Gaussian tail by its elementary Mills-ratio majorant.
-/
lemma gaussianTail_le {x : ℝ} (hx : 0 < x) :
    (∫ s : ℝ in Set.Ioi x, gaussianKernel s) ≤ gaussianKernel x / (4 * x) := by
  have hmoment : MeasureTheory.Integrable (fun s : ℝ => s * gaussianKernel s) := by
    simpa only [gaussianKernel] using
      integrable_mul_exp_neg_mul_sq (b := (2 : ℝ)) (by norm_num)
  have hscaled : MeasureTheory.IntegrableOn
      (fun s : ℝ => (1 / x) * (s * gaussianKernel s)) (Set.Ioi x) :=
    (hmoment.const_mul (1 / x)).integrableOn
  have hmono := MeasureTheory.setIntegral_mono_on
    gaussianKernel_integrable.integrableOn hscaled measurableSet_Ioi
    (fun s hs => by
      have hslt : x < s := hs
      have hsx : 1 ≤ s / x := (le_div_iff₀ hx).2 (by simpa using le_of_lt hslt)
      calc
        gaussianKernel s ≤ (s / x) * gaussianKernel s :=
          le_mul_of_one_le_left (Real.exp_pos _).le hsx
        _ = (1 / x) * (s * gaussianKernel s) := by ring)
  calc
    (∫ s : ℝ in Set.Ioi x, gaussianKernel s) ≤
        ∫ s : ℝ in Set.Ioi x, (1 / x) * (s * gaussianKernel s) := hmono
    _ = (1 / x) * (∫ s : ℝ in Set.Ioi x, s * gaussianKernel s) := by
      rw [MeasureTheory.integral_const_mul]
    _ = gaussianKernel x / (4 * x) := by
      rw [gaussianFirstMoment_tail]
      field_simp [hx.ne']

/-- NODE HE.CompactSupportConstruction.distinguished_exterior_profile_positive
deps: HE.CompactSupportConstruction.gaussian_half_mass_tail_identity, HE.CompactSupportConstruction.gaussian_tail_positive
statement: the distinguished exterior mode is strictly positive on the right half-line.
-/
lemma exteriorProfile_halfMass_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < exteriorProfile gaussianHalfMass x := by
  unfold exteriorProfile
  rw [gaussianHalfMass_sub_primitive hx]
  exact mul_pos (Real.exp_pos _) (gaussianTail_pos x)

/-- NODE HE.CompactSupportConstruction.distinguished_exterior_profile_mills_bound
deps: HE.CompactSupportConstruction.gaussian_half_mass_tail_identity, HE.CompactSupportConstruction.gaussian_tail_mills_bound
statement: the distinguished exterior mode has the critical reciprocal decay bound.
-/
lemma exteriorProfile_halfMass_le {x : ℝ} (hx : 0 < x) :
    exteriorProfile gaussianHalfMass x ≤ 1 / (4 * x) := by
  unfold exteriorProfile
  rw [gaussianHalfMass_sub_primitive hx.le]
  have htail := gaussianTail_le hx
  have hcancel : Real.exp (2 * x^2) * gaussianKernel x = 1 := by
    unfold gaussianKernel
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    Real.exp (2 * x^2) * (∫ s : ℝ in Set.Ioi x, gaussianKernel s) ≤
        Real.exp (2 * x^2) * (gaussianKernel x / (4 * x)) :=
      mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = (Real.exp (2 * x^2) * gaussianKernel x) / (4 * x) := by ring
    _ = 1 / (4 * x) := by rw [hcancel]

/-- NODE HE.CompactSupportConstruction.gaussian_kernel_derivative
deps:
statement: compute the derivative of the Gaussian kernel.
-/
lemma gaussianKernel_hasDerivAt (x : ℝ) :
    HasDerivAt gaussianKernel (-4 * x * gaussianKernel x) x := by
  unfold gaussianKernel
  have hinnerRaw :=
    ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (-2)
  have hinner : HasDerivAt (fun y : ℝ => -2 * (y * y))
      (-2 * (x + x)) x := by
    simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using hinnerRaw
  have h := (Real.hasDerivAt_exp (-2 * (x * x))).comp x hinner
  convert h using 1 <;>
    first | rfl | (funext y; simp [Function.comp_def, pow_two]) | ring

lemma gaussianPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt gaussianPrimitive (gaussianKernel x) x := by
  unfold gaussianPrimitive
  exact (gaussianKernel_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- NODE HE.CompactSupportConstruction.gaussian_primitive_smooth
deps: HE.CompactSupportConstruction.gaussian_kernel_derivative
statement: the finite-interval Gaussian primitive is infinitely differentiable.
-/
lemma gaussianPrimitive_smooth : ContDiff ℝ ∞ gaussianPrimitive := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro x
    exact (gaussianPrimitive_hasDerivAt x).differentiableAt
  · have hderiv : deriv gaussianPrimitive = gaussianKernel := by
      funext x
      exact (gaussianPrimitive_hasDerivAt x).deriv
    rw [hderiv]
    unfold gaussianKernel
    fun_prop

/-- NODE HE.CompactSupportConstruction.exterior_profile_smooth
deps: HE.CompactSupportConstruction.gaussian_primitive_smooth
statement: every Gaussian-tail exterior profile is infinitely differentiable.
-/
lemma exteriorProfile_smooth (C : ℝ) : ContDiff ℝ ∞ (exteriorProfile C) := by
  unfold exteriorProfile
  have hExp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (2 * x^2)) := by fun_prop
  exact hExp.mul (contDiff_const.sub gaussianPrimitive_smooth)

/-- NODE HE.CompactSupportConstruction.exterior_profile_first_derivative
deps: HE.CompactSupportConstruction.gaussian_kernel_derivative
statement: compute the first derivative of the Gaussian-tail exterior profile.
-/
lemma exteriorProfile_hasDerivAt (C x : ℝ) :
    HasDerivAt (exteriorProfile C)
      (4 * x * exteriorProfile C x - 1) x := by
  have hExpDiff : DifferentiableAt ℝ
      (fun y : ℝ => Real.exp (2 * y^2)) x := by fun_prop
  have hTailDiff : DifferentiableAt ℝ
      (fun y : ℝ => C - gaussianPrimitive y) x :=
    (differentiableAt_const C).sub (gaussianPrimitive_hasDerivAt x).differentiableAt
  have hdiff : DifferentiableAt ℝ (exteriorProfile C) x := by
    unfold exteriorProfile
    exact hExpDiff.mul hTailDiff
  refine hdiff.hasDerivAt.congr_deriv ?_
  have hExpDeriv :
      deriv (fun y : ℝ => Real.exp (2 * y^2)) x =
        4 * x * Real.exp (2 * x^2) := by
    rw [deriv_exp]
    · have hinner : deriv (fun y : ℝ => 2 * y^2) x = 4 * x := by
        simp
        ring
      rw [hinner]
      ring
    · fun_prop
  have hTailDeriv :
      deriv (fun y : ℝ => C - gaussianPrimitive y) x =
        -gaussianKernel x := by
    rw [show deriv (fun y : ℝ => C - gaussianPrimitive y) x =
        -deriv gaussianPrimitive x by
          simpa using
            (deriv_const_sub (f := gaussianPrimitive) (x := x) C)]
    rw [(gaussianPrimitive_hasDerivAt x).deriv]
  have hcancel : Real.exp (2 * x^2) * gaussianKernel x = 1 := by
    unfold gaussianKernel
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [show deriv (exteriorProfile C) x =
      deriv (fun y : ℝ => Real.exp (2 * y^2)) x *
          (C - gaussianPrimitive x) +
        Real.exp (2 * x^2) *
          deriv (fun y : ℝ => C - gaussianPrimitive y) x by
      unfold exteriorProfile
      exact deriv_fun_mul hExpDiff hTailDiff]
  rw [hExpDeriv, hTailDeriv]
  unfold exteriorProfile
  calc
    4 * x * Real.exp (2 * x^2) * (C - gaussianPrimitive x) +
          Real.exp (2 * x^2) * -gaussianKernel x =
        4 * x * (Real.exp (2 * x^2) * (C - gaussianPrimitive x)) -
          Real.exp (2 * x^2) * gaussianKernel x := by ring
    _ = 4 * x * (Real.exp (2 * x^2) * (C - gaussianPrimitive x)) - 1 := by
      rw [hcancel]

lemma exteriorProfile_deriv (C x : ℝ) :
    deriv (exteriorProfile C) x = 4 * x * exteriorProfile C x - 1 :=
  (exteriorProfile_hasDerivAt C x).deriv

/-- NODE HE.CompactSupportConstruction.exterior_profile_second_derivative
deps: HE.CompactSupportConstruction.exterior_profile_first_derivative
statement: differentiate the first-derivative formula for the exterior profile.
-/
lemma exteriorProfile_first_hasDerivAt (C x : ℝ) :
    HasDerivAt (fun y : ℝ => 4 * y * exteriorProfile C y - 1)
      (4 * exteriorProfile C x + 4 * x *
        (4 * x * exteriorProfile C x - 1)) x := by
  have hLinearDiff : DifferentiableAt ℝ (fun y : ℝ => 4 * y) x := by fun_prop
  have hProfileDiff : DifferentiableAt ℝ (exteriorProfile C) x :=
    (exteriorProfile_hasDerivAt C x).differentiableAt
  have hProductDiff : DifferentiableAt ℝ
      (fun y : ℝ => 4 * y * exteriorProfile C y) x :=
    hLinearDiff.mul hProfileDiff
  have hdiff : DifferentiableAt ℝ
      (fun y : ℝ => 4 * y * exteriorProfile C y - 1) x :=
    hProductDiff.sub (differentiableAt_const 1)
  refine hdiff.hasDerivAt.congr_deriv ?_
  rw [deriv_fun_sub hProductDiff (differentiableAt_const 1)]
  rw [deriv_fun_mul hLinearDiff hProfileDiff]
  rw [(exteriorProfile_hasDerivAt C x).deriv]
  simp

/-- NODE HE.CompactSupportConstruction.exterior_profile_second_deriv_value
deps: HE.CompactSupportConstruction.exterior_profile_first_derivative, HE.CompactSupportConstruction.exterior_profile_second_derivative
statement: identify the second derivative of the exterior profile.
-/
lemma exteriorProfile_second_deriv (C x : ℝ) :
    deriv (deriv (exteriorProfile C)) x =
      4 * exteriorProfile C x +
        4 * x * (4 * x * exteriorProfile C x - 1) := by
  have hfirst : deriv (exteriorProfile C) =
      fun y : ℝ => 4 * y * exteriorProfile C y - 1 := by
    funext y
    exact (exteriorProfile_hasDerivAt C y).deriv
  rw [hfirst]
  exact (exteriorProfile_first_hasDerivAt C x).deriv

/-- NODE HE.CompactSupportConstruction.exterior_profile_ode
deps: HE.CompactSupportConstruction.exterior_profile_first_derivative, HE.CompactSupportConstruction.exterior_profile_second_deriv_value
statement: the Gaussian-tail exterior profile solves the constant-remainder ODE needed to make the potential vanish.
-/
theorem exteriorProfile_ode (C x : ℝ) :
    deriv (deriv (exteriorProfile C)) x -
        4 * x * deriv (exteriorProfile C) x =
      4 * exteriorProfile C x := by
  rw [exteriorProfile_second_deriv, exteriorProfile_deriv]
  ring

/-! ## Exterior oscillator profile -/

/-- The actual exterior Schrödinger profile, obtained after restoring the
Gaussian factor removed in the tail equation. -/
def exteriorMasterProfile (C x : ℝ) : ℝ :=
  Real.exp (-x^2) * exteriorProfile C x

/-- NODE HE.CompactSupportConstruction.critical_weight_cancels_exterior_gaussian
deps:
statement: the critical Gaussian weight exactly cancels the Gaussian factor in the master profile.
-/
lemma weightedExteriorMaster_eq (C x : ℝ) :
    Real.exp (x^2) * exteriorMasterProfile C x = exteriorProfile C x := by
  unfold exteriorMasterProfile
  have hcancel : Real.exp (x^2) * Real.exp (-x^2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [← mul_assoc, hcancel, one_mul]

/-- NODE HE.CompactSupportConstruction.exterior_master_smooth
deps: HE.CompactSupportConstruction.exterior_profile_smooth
statement: every Gaussian-weighted exterior master profile is infinitely differentiable.
-/
lemma exteriorMasterProfile_smooth (C : ℝ) :
    ContDiff ℝ ∞ (exteriorMasterProfile C) := by
  unfold exteriorMasterProfile
  have hExp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-x^2)) := by fun_prop
  exact hExp.mul (exteriorProfile_smooth C)

/-- NODE HE.CompactSupportConstruction.distinguished_exterior_master_positive
deps: HE.CompactSupportConstruction.distinguished_exterior_profile_positive
statement: the Gaussian-weighted distinguished exterior profile is positive on the right half-line.
-/
lemma exteriorMasterProfile_halfMass_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < exteriorMasterProfile gaussianHalfMass x := by
  unfold exteriorMasterProfile
  exact mul_pos (Real.exp_pos _) (exteriorProfile_halfMass_pos hx)

/-- Its explicit first derivative. -/
def exteriorMasterFirst (C x : ℝ) : ℝ :=
  Real.exp (-x^2) * (2 * x * exteriorProfile C x - 1)

/-- NODE HE.CompactSupportConstruction.exterior_master_first_derivative
deps: HE.CompactSupportConstruction.exterior_profile_first_derivative
statement: differentiate the Gaussian-weighted exterior master profile.
-/
lemma exteriorMasterProfile_hasDerivAt (C x : ℝ) :
    HasDerivAt (exteriorMasterProfile C) (exteriorMasterFirst C x) x := by
  have hGaussian : HasDerivAt (fun y : ℝ => Real.exp (-y^2))
      (-2 * x * Real.exp (-x^2)) x := by
    have hinnerRaw :=
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (-1)
    have hinner : HasDerivAt (fun y : ℝ => -1 * (y * y))
        (-1 * (x + x)) x := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using hinnerRaw
    have h := (Real.hasDerivAt_exp (-1 * (x * x))).comp x hinner
    convert h using 1 <;>
      first | rfl | (funext y; simp [Function.comp_def, pow_two]) | ring
  have h := hGaussian.mul (exteriorProfile_hasDerivAt C x)
  unfold exteriorMasterProfile exteriorMasterFirst
  convert h using 1 <;> first | rfl | ring

/-- NODE HE.CompactSupportConstruction.exterior_master_second_derivative
deps: HE.CompactSupportConstruction.exterior_master_first_derivative, HE.CompactSupportConstruction.exterior_profile_first_derivative
statement: differentiate the explicit first derivative of the exterior master profile.
-/
lemma exteriorMasterFirst_hasDerivAt (C x : ℝ) :
    HasDerivAt (exteriorMasterFirst C)
      ((4 * x^2 + 2) * exteriorMasterProfile C x) x := by
  have hGaussian : HasDerivAt (fun y : ℝ => Real.exp (-y^2))
      (-2 * x * Real.exp (-x^2)) x := by
    have hinnerRaw :=
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (-1)
    have hinner : HasDerivAt (fun y : ℝ => -1 * (y * y))
        (-1 * (x + x)) x := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using hinnerRaw
    have h := (Real.hasDerivAt_exp (-1 * (x * x))).comp x hinner
    convert h using 1 <;>
      first | rfl | (funext y; simp [Function.comp_def, pow_two]) | ring
  have hBracket : HasDerivAt
      (fun y : ℝ => 2 * y * exteriorProfile C y - 1)
      (2 * exteriorProfile C x +
        2 * x * (4 * x * exteriorProfile C x - 1)) x := by
    have h := (((hasDerivAt_id x).const_mul 2).mul
      (exteriorProfile_hasDerivAt C x)).sub_const 1
    convert h using 1 <;> first | rfl | simp | ring
  have h := hGaussian.mul hBracket
  unfold exteriorMasterProfile exteriorMasterFirst
  convert h using 1 <;> first | rfl | ring

/-- NODE HE.CompactSupportConstruction.exterior_master_ode
deps: HE.CompactSupportConstruction.exterior_master_first_derivative, HE.CompactSupportConstruction.exterior_master_second_derivative
statement: the Gaussian-weighted exterior profile has constant master remainder two.
-/
theorem exteriorMasterProfile_ode (C x : ℝ) :
    deriv (deriv (exteriorMasterProfile C)) x =
      (4 * x^2 + 2) * exteriorMasterProfile C x := by
  have hfirst : deriv (exteriorMasterProfile C) = exteriorMasterFirst C := by
    funext y
    exact (exteriorMasterProfile_hasDerivAt C y).deriv
  rw [hfirst]
  exact (exteriorMasterFirst_hasDerivAt C x).deriv


end CompactSupportConstruction
end HardyCompactSupport

