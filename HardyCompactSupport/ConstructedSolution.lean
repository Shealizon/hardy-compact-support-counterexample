import HardyCompactSupport.PositiveProfile
import HardyCompactSupport.ExplicitSolution

/-!
# Constructed solution and potential
-/

noncomputable section

namespace HardyCompactSupport
namespace CompactSupportConstruction

open intervalIntegral
open Filter
open scoped ContDiff

/-! ## Fixed theorem statement and proof graph -/

/--
The static data needed by the normalized one-dimensional master construction.
The difficult existence theorem below must eventually construct this data by
gluing the two Gaussian-tail exterior profiles through a smooth positive
interior profile.
-/
structure CompactProfileData where
  profile : ℝ → ℝ
  profileFirst : ℝ → ℝ
  profileSecond : ℝ → ℝ
  remainder : ℝ → ℝ
  remainderInf : ℝ
  radius : ℝ
  remainderBound : ℝ
  radius_pos : 0 < radius
  remainderBound_nonneg : 0 ≤ remainderBound
  profile_smooth : ContDiff ℝ ∞ profile
  remainder_smooth : ContDiff ℝ ∞ remainder
  profile_hasDerivAt : ∀ x : ℝ, HasDerivAt profile (profileFirst x) x
  profileFirst_hasDerivAt : ∀ x : ℝ, HasDerivAt profileFirst (profileSecond x) x
  oscillator_identity : ∀ x : ℝ,
    profileSecond x = (4 * x^2 + remainder x) * profile x
  profile_zero_ne : profile 0 ≠ 0
  remainder_bounded : ∀ x : ℝ, |remainder x - remainderInf| ≤ remainderBound
  remainder_exterior : ∀ x : ℝ, radius ≤ |x| → remainder x = remainderInf
  endpoint_integrable : MeasureTheory.Integrable
    (fun x : ℝ => (Real.exp (x^2) * profile x)^2)

/-- The normalized transported amplitude associated with a compact profile. -/
def compactAmplitude (P : CompactProfileData) (t x : ℝ) : ℝ :=
  (1 / Real.sqrt (TimeScaling.ySym t)) * P.profile (ExplicitSolution.endpointScale t x)

/-- The normalized quadratic phase with the master time correction. -/
def compactPhase (P : CompactProfileData) (t x : ℝ) : ℝ :=
  ExplicitSolution.endpointB t * x^2 +
    (P.remainderInf / 4) * Real.arctan (2 * t - 1)

/-- The complex-valued candidate solution. -/
def compactSolution (P : CompactProfileData) (t x : ℝ) : ℂ :=
  (compactAmplitude P t x : ℂ) *
    Complex.exp (Complex.I * (compactPhase P t x : ℂ))

/-- The real scalar candidate potential. -/
def compactPotential (P : CompactProfileData) (t x : ℝ) : ℝ :=
  (P.remainder (ExplicitSolution.endpointScale t x) - P.remainderInf) /
    (TimeScaling.ySym t)^2

/-- The actual normalized theorem, fixed before the remaining proof is filled.

It states existence of a nonzero smooth solution on the normalized time
interval `[0,1]`, together with a smooth bounded real scalar potential whose
spatial support at time `t` lies in `|x| ≤ R y(t)`.  The pointwise
Schrödinger equation and both critical Gaussian endpoint integrals are part of
the statement, not deferred to informal interpretation.
-/
def NormalizedCompactEndpointStatement : Prop :=
  ∃ (u : ℝ → ℝ → ℂ) (V : ℝ → ℝ → ℝ) (R C : ℝ),
    0 < R ∧
    0 ≤ C ∧
    ContDiff ℝ ∞ (Function.uncurry u) ∧
    ContDiff ℝ ∞ (Function.uncurry V) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ x : ℝ, u t x ≠ 0) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      Complex.I * deriv (fun τ : ℝ => u τ x) t +
          deriv (deriv (fun ξ : ℝ => u t ξ)) x =
        (V t x : ℂ) * u t x) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, |V t x| ≤ C) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      R * TimeScaling.ySym t < |x| → V t x = 0) ∧
    MeasureTheory.Integrable
      (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 0 x‖^2) ∧
    MeasureTheory.Integrable
      (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 1 x‖^2)

/-- NODE HE.CompactSupportConstruction.profile_data_exists
deps: HE.CompactSupportConstruction.exterior_profile_ode
statement: construct the smooth positive one-dimensional profile with constant exterior remainder and critical weighted integrability.
-/
theorem compactProfileData_exists : Nonempty CompactProfileData := by
  rcases gluedRemainder_bounded_exists with ⟨B, hBnonneg, hB⟩
  refine ⟨{
    profile := gluedProfile
    profileFirst := gluedProfileFirst
    profileSecond := gluedProfileSecond
    remainder := gluedRemainder
    remainderInf := 2
    radius := 3
    remainderBound := B
    radius_pos := by norm_num
    remainderBound_nonneg := hBnonneg
    profile_smooth := gluedProfile_smooth
    remainder_smooth := gluedRemainder_smooth
    profile_hasDerivAt := fun x => (gluedProfile_derivative_data x).1
    profileFirst_hasDerivAt := fun x => (gluedProfile_derivative_data x).2
    oscillator_identity := gluedProfile_oscillator_identity
    profile_zero_ne := by rw [gluedProfile_zero]; norm_num
    remainder_bounded := hB
    remainder_exterior := gluedRemainder_exterior
    endpoint_integrable := by
      change MeasureTheory.Integrable gluedWeightedSquare
      exact gluedWeightedSquare_integrable }⟩

/-- Fix the profile supplied by the difficult static construction. -/
noncomputable def compactProfileData : CompactProfileData :=
  Classical.choice compactProfileData_exists

/-! ## Smooth transported candidate -/

lemma compactYSmooth : ContDiff ℝ ∞ TimeScaling.ySym := by
  have hq : ContDiff ℝ ∞ TimeScaling.qSym := by
    unfold TimeScaling.qSym
    fun_prop
  have hsqrt : ContDiff ℝ ∞ (fun t => Real.sqrt (TimeScaling.qSym t)) :=
    hq.sqrt (fun t => ne_of_gt (TimeScaling.symmetric_q_pos t))
  unfold TimeScaling.ySym
  exact contDiff_const.mul hsqrt

lemma compactScaleSmooth : ContDiff ℝ ∞
    (Function.uncurry ExplicitSolution.endpointScale) := by
  apply ContDiff.div (by fun_prop) (compactYSmooth.comp (by fun_prop))
  intro p
  exact TimeScaling.symmetric_y_ne_zero p.1

lemma compactBSmooth : ContDiff ℝ ∞ ExplicitSolution.endpointB := by
  unfold ExplicitSolution.endpointB
  have hq : ContDiff ℝ ∞ TimeScaling.qSym := by
    unfold TimeScaling.qSym
    fun_prop
  apply ContDiff.div (by fun_prop) (contDiff_const.mul hq)
  intro t
  exact mul_ne_zero (by norm_num) (TimeScaling.symmetric_q_ne_zero t)

/-- NODE HE.CompactSupportConstruction.candidate_smooth
deps: HE.CompactSupportConstruction.profile_data_exists
statement: the transported candidate solution and its real scalar potential are smooth.
-/
theorem compactCandidate_smooth :
    ContDiff ℝ ∞ (Function.uncurry (compactSolution compactProfileData)) ∧
    ContDiff ℝ ∞ (Function.uncurry (compactPotential compactProfileData)) := by
  have hscale := compactScaleSmooth
  have hprofile : ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        compactProfileData.profile (Function.uncurry ExplicitSolution.endpointScale p)) := by
    simpa [Function.comp_def] using compactProfileData.profile_smooth.comp hscale
  have hrem : ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        compactProfileData.remainder (Function.uncurry ExplicitSolution.endpointScale p)) := by
    simpa [Function.comp_def] using compactProfileData.remainder_smooth.comp hscale
  have hsqrtY : ContDiff ℝ ∞ (fun t => Real.sqrt (TimeScaling.ySym t)) :=
    compactYSmooth.sqrt (fun t => TimeScaling.symmetric_y_ne_zero t)
  have hinvSqrt : ContDiff ℝ ∞ (fun t => 1 / Real.sqrt (TimeScaling.ySym t)) := by
    apply ContDiff.div contDiff_const hsqrtY
    intro t
    exact ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos t))
  have hamp : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => compactAmplitude compactProfileData p.1 p.2) := by
    unfold compactAmplitude
    exact (hinvSqrt.comp (by fun_prop)).mul hprofile
  have hphase : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => compactPhase compactProfileData p.1 p.2) := by
    unfold compactPhase
    exact ((compactBSmooth.comp (by fun_prop)).mul (by fun_prop)).add
      (contDiff_const.mul (Real.contDiff_arctan.comp (by fun_prop)))
  have hampC : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => (compactAmplitude compactProfileData p.1 p.2 : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hamp
  have hphaseC : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => (compactPhase compactProfileData p.1 p.2 : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hphase
  constructor
  · unfold compactSolution
    exact hampC.mul (Complex.contDiff_exp.comp (contDiff_const.mul hphaseC))
  · unfold compactPotential
    apply (hrem.sub contDiff_const).div
      ((compactYSmooth.comp (by fun_prop)).pow 2)
    intro p
    exact pow_ne_zero 2 (TimeScaling.symmetric_y_ne_zero p.1)

/-- NODE HE.CompactSupportConstruction.candidate_nonzero
deps: HE.CompactSupportConstruction.profile_data_exists
statement: the transported candidate is nonzero on the normalized time interval.
-/
theorem compactCandidate_nonzero :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ x : ℝ,
      compactSolution compactProfileData t x ≠ 0 := by
  refine ⟨0, by norm_num, 0, ?_⟩
  unfold compactSolution compactAmplitude compactPhase ExplicitSolution.endpointScale
  apply mul_ne_zero
  · simp only [zero_div]
    exact_mod_cast mul_ne_zero
      (one_div_ne_zero (ne_of_gt
        (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos 0))))
      compactProfileData.profile_zero_ne
  · exact Complex.exp_ne_zero _


end CompactSupportConstruction
end HardyCompactSupport

