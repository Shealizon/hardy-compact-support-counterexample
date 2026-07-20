import HardyCompactSupport.SchrodingerIdentity

/-!
# Boundedness, exterior vanishing, and endpoint decay
-/

noncomputable section

namespace HardyCompactSupport
namespace CompactSupportConstruction

open intervalIntegral
open Filter
open scoped ContDiff

/-- NODE HE.CompactSupportConstruction.candidate_bounded
deps: HE.CompactSupportConstruction.profile_data_exists
statement: the candidate real scalar potential is uniformly bounded on the normalized time interval.
-/
theorem compactCandidate_bounded :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      |compactPotential compactProfileData t x| ≤
        compactProfileData.remainderBound := by
  intro t _ x
  have hrem := compactProfileData.remainder_bounded (ExplicitSolution.endpointScale t x)
  have hySq : 1 ≤ (TimeScaling.ySym t)^2 := by
    rw [TimeScaling.symmetric_y_sq]
    unfold TimeScaling.qSym
    nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
  have hySqPos : 0 < (TimeScaling.ySym t)^2 := lt_of_lt_of_le zero_lt_one hySq
  have hySqAbs : |(TimeScaling.ySym t)^2| = (TimeScaling.ySym t)^2 :=
    abs_of_nonneg (sq_nonneg _)
  unfold compactPotential
  rw [abs_div, hySqAbs]
  apply (div_le_iff₀ hySqPos).2
  nlinarith [compactProfileData.remainderBound_nonneg]

/-- NODE HE.CompactSupportConstruction.candidate_compact_support
deps: HE.CompactSupportConstruction.profile_data_exists
statement: the candidate potential vanishes outside the moving compact interval determined by the profile radius.
-/
theorem compactCandidate_compact_support :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      compactProfileData.radius * TimeScaling.ySym t < |x| →
        compactPotential compactProfileData t x = 0 := by
  intro t _ x hx
  have hy : 0 < TimeScaling.ySym t := TimeScaling.symmetric_y_pos t
  have hscale : compactProfileData.radius ≤ |ExplicitSolution.endpointScale t x| := by
    unfold ExplicitSolution.endpointScale
    rw [abs_div, abs_of_pos hy]
    exact le_of_lt ((lt_div_iff₀ hy).2 hx)
  unfold compactPotential
  rw [compactProfileData.remainder_exterior _ hscale]
  simp

/-- NODE HE.CompactSupportConstruction.candidate_endpoint_integrable
deps: HE.CompactSupportConstruction.profile_data_exists
statement: both normalized critical Gaussian endpoint squares are integrable.
-/
lemma compactEndpointZeroNormSq (x : ℝ) :
    ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) *
        compactSolution compactProfileData 0 x‖^2 =
      (1 / 2 : ℝ) *
        (Real.exp ((x / 2)^2) * compactProfileData.profile (x / 2))^2 := by
  unfold compactSolution compactAmplitude compactPhase ExplicitSolution.endpointScale
    ExplicitSolution.endpointB TimeScaling.ySym TimeScaling.qSym
  simp only [norm_mul, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcast : (x : ℂ)^2 / 4 = ((x^2 / 4 : ℝ) : ℂ) := by norm_num
  have hsqRe : (((x : ℂ)^2).re : ℝ) = x^2 := by
    simp [pow_two, Complex.mul_re]
  have hsqIm : (((x : ℂ)^2).im : ℝ) = 0 := by
    simp [pow_two, Complex.mul_im]
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [hcast, Complex.norm_exp, hsqIm, abs_of_pos hsqrtPos]
  norm_num
  field_simp [ne_of_gt hsqrtPos]
  rw [hsqRe, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma compactEndpointOneNormSq (x : ℝ) :
    ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) *
        compactSolution compactProfileData 1 x‖^2 =
      (1 / 2 : ℝ) *
        (Real.exp ((x / 2)^2) * compactProfileData.profile (x / 2))^2 := by
  unfold compactSolution compactAmplitude compactPhase ExplicitSolution.endpointScale
    ExplicitSolution.endpointB TimeScaling.ySym TimeScaling.qSym
  simp only [norm_mul, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcast : (x : ℂ)^2 / 4 = ((x^2 / 4 : ℝ) : ℂ) := by norm_num
  have hsqRe : (((x : ℂ)^2).re : ℝ) = x^2 := by
    simp [pow_two, Complex.mul_re]
  have hsqIm : (((x : ℂ)^2).im : ℝ) = 0 := by
    simp [pow_two, Complex.mul_im]
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [hcast, Complex.norm_exp, hsqIm, abs_of_pos hsqrtPos]
  norm_num
  field_simp [ne_of_gt hsqrtPos]
  rw [hsqRe, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem compactCandidate_endpoint_integrable :
    MeasureTheory.Integrable
        (fun x : ℝ =>
          ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) *
            compactSolution compactProfileData 0 x‖^2) ∧
      MeasureTheory.Integrable
        (fun x : ℝ =>
          ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) *
            compactSolution compactProfileData 1 x‖^2) := by
  have hscaled : MeasureTheory.Integrable
      (fun x : ℝ =>
        (Real.exp ((x / 2)^2) * compactProfileData.profile (x / 2))^2) :=
    compactProfileData.endpoint_integrable.comp_div (by norm_num)
  have hhalf := hscaled.const_mul (1 / 2 : ℝ)
  constructor
  · simpa only [compactEndpointZeroNormSq] using hhalf
  · simpa only [compactEndpointOneNormSq] using hhalf

/-- NODE HE.CompactSupportConstruction.normalized_compact_endpoint
deps: HE.CompactSupportConstruction.candidate_smooth, HE.CompactSupportConstruction.candidate_nonzero, HE.CompactSupportConstruction.candidate_schrodinger, HE.CompactSupportConstruction.candidate_bounded, HE.CompactSupportConstruction.candidate_compact_support, HE.CompactSupportConstruction.candidate_endpoint_integrable
statement: a nonzero normalized one-dimensional Hardy endpoint solution exists with a smooth bounded compactly supported real scalar potential.
-/
theorem normalized_compact_endpoint : NormalizedCompactEndpointStatement := by
  refine ⟨compactSolution compactProfileData,
    compactPotential compactProfileData,
    compactProfileData.radius,
    compactProfileData.remainderBound,
    compactProfileData.radius_pos,
    compactProfileData.remainderBound_nonneg, ?_⟩
  exact ⟨compactCandidate_smooth.1,
    compactCandidate_smooth.2,
    compactCandidate_nonzero,
    compactCandidate_schrodinger,
    compactCandidate_bounded,
    compactCandidate_compact_support,
    compactCandidate_endpoint_integrable.1,
    compactCandidate_endpoint_integrable.2⟩


end CompactSupportConstruction
end HardyCompactSupport

