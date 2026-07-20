import HardyCompactSupport.ConstructedSolution

/-!
# Schrodinger equation identity
-/

noncomputable section

namespace HardyCompactSupport
namespace CompactSupportConstruction

open intervalIntegral
open Filter
open scoped ContDiff

/-! ## Derivatives of the transported candidate -/

/-- NODE HE.CompactSupportConstruction.compact_phase_x_deriv
deps:
statement: compute the first spatial derivative of the compact candidate phase.
-/
lemma compactPhase_x_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun ξ : ℝ => compactPhase P t ξ) x =
      2 * ExplicitSolution.endpointB t * x := by
  unfold compactPhase
  simp
  ring

/-- NODE HE.CompactSupportConstruction.compact_phase_x_second_deriv
deps: HE.CompactSupportConstruction.compact_phase_x_deriv
statement: compute the second spatial derivative of the compact candidate phase.
-/
lemma compactPhase_x_second_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => compactPhase P t ξ)) x =
      2 * ExplicitSolution.endpointB t := by
  have hfun : deriv (fun ξ : ℝ => compactPhase P t ξ) =
      fun ξ : ℝ => 2 * ExplicitSolution.endpointB t * ξ := by
    funext ξ
    exact compactPhase_x_deriv P t ξ
  rw [hfun]
  simp

/-- NODE HE.CompactSupportConstruction.compact_phase_t_deriv
deps:
statement: compute the time derivative of the compact candidate phase.
-/
lemma compactPhase_t_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun τ : ℝ => compactPhase P τ x) t =
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        P.remainderInf / (4 * TimeScaling.qSym t) := by
  unfold compactPhase
  change deriv (((fun τ : ℝ => ExplicitSolution.endpointB τ * x^2) +
    (fun τ : ℝ => (P.remainderInf / 4) * Real.arctan (2 * τ - 1)))) t =
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
        P.remainderInf / (4 * TimeScaling.qSym t)
  have hArctan : DifferentiableAt ℝ
      (fun τ : ℝ => Real.arctan (2 * τ - 1)) t := by
    exact (show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
      fun_prop).arctan
  rw [deriv_add]
  · rw [deriv_mul_const]
    · rw [ExplicitSolution.endpointB_deriv]
      rw [deriv_const_mul]
      · rw [deriv_arctan]
        · rw [show deriv (fun τ : ℝ => 2 * τ - 1) t = 2 by simp]
          have hq : TimeScaling.qSym t ≠ 0 := TimeScaling.symmetric_q_ne_zero t
          unfold TimeScaling.qSym at hq ⊢
          field_simp [hq]
          ring
        · fun_prop
      · exact hArctan
    · exact ExplicitSolution.endpointB_differentiableAt t
  · exact (ExplicitSolution.endpointB_differentiableAt t).mul (differentiableAt_const _)
  · exact hArctan.const_mul (P.remainderInf / 4)

/-- NODE HE.CompactSupportConstruction.compact_amplitude_x_deriv
deps:
statement: compute the first spatial derivative of the transported compact amplitude.
-/
lemma compactAmplitude_x_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun ξ : ℝ => compactAmplitude P t ξ) x =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        P.profileFirst (ExplicitSolution.endpointScale t x) / TimeScaling.ySym t := by
  have hscale : HasDerivAt (fun ξ : ℝ => ExplicitSolution.endpointScale t ξ)
      (1 / TimeScaling.ySym t) x := by
    unfold ExplicitSolution.endpointScale
    simpa using (hasDerivAt_id x).div_const (TimeScaling.ySym t)
  have hprofile := (P.profile_hasDerivAt (ExplicitSolution.endpointScale t x)).comp x hscale
  have hprofileDeriv :
      deriv (fun ξ : ℝ => P.profile (ExplicitSolution.endpointScale t ξ)) x =
        P.profileFirst (ExplicitSolution.endpointScale t x) * (1 / TimeScaling.ySym t) := by
    simpa [Function.comp_def] using hprofile.deriv
  unfold compactAmplitude
  rw [deriv_const_mul]
  · rw [hprofileDeriv]
    ring
  · exact hprofile.differentiableAt

/-- NODE HE.CompactSupportConstruction.compact_amplitude_x_second_deriv
deps: HE.CompactSupportConstruction.compact_amplitude_x_deriv
statement: compute the second spatial derivative of the transported compact amplitude.
-/
lemma compactAmplitude_x_second_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => compactAmplitude P t ξ)) x =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        P.profileSecond (ExplicitSolution.endpointScale t x) / (TimeScaling.ySym t)^2 := by
  have hfun : deriv (fun ξ : ℝ => compactAmplitude P t ξ) =
      fun ξ : ℝ => (1 / Real.sqrt (TimeScaling.ySym t)) *
        P.profileFirst (ExplicitSolution.endpointScale t ξ) / TimeScaling.ySym t := by
    funext ξ
    exact compactAmplitude_x_deriv P t ξ
  rw [hfun]
  have hscale : HasDerivAt (fun ξ : ℝ => ExplicitSolution.endpointScale t ξ)
      (1 / TimeScaling.ySym t) x := by
    unfold ExplicitSolution.endpointScale
    simpa using (hasDerivAt_id x).div_const (TimeScaling.ySym t)
  have hsecond := (P.profileFirst_hasDerivAt (ExplicitSolution.endpointScale t x)).comp x hscale
  have hwhole := (hsecond.const_mul
    (1 / Real.sqrt (TimeScaling.ySym t))).div_const (TimeScaling.ySym t)
  have hvalue := hwhole.deriv
  convert hvalue using 1 <;> simp <;> ring

/-- NODE HE.CompactSupportConstruction.compact_amplitude_t_deriv
deps:
statement: compute the time derivative of the transported compact amplitude.
-/
lemma compactAmplitude_t_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun τ : ℝ => compactAmplitude P τ x) t =
      (1 / Real.sqrt (TimeScaling.ySym t)) *
        (-(deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t)) *
            P.profile (ExplicitSolution.endpointScale t x) +
          P.profileFirst (ExplicitSolution.endpointScale t x) *
            (-x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2)) := by
  have hwidth : DifferentiableAt ℝ
      (fun τ : ℝ => 1 / Real.sqrt (TimeScaling.ySym τ)) t := by
    have hy : TimeScaling.ySym t ≠ 0 := TimeScaling.symmetric_y_ne_zero t
    have hsqrt : Real.sqrt (TimeScaling.ySym t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos t))
    exact (differentiableAt_const (1 : ℝ)).div
      ((TimeScaling.ySym_hasDerivAt t).differentiableAt.sqrt hy) hsqrt
  have hscale : HasDerivAt (fun τ : ℝ => ExplicitSolution.endpointScale τ x)
      (-x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2) t := by
    have hd := ExplicitSolution.endpointScale_differentiableAt_t t x
    simpa [ExplicitSolution.endpointScale_t_deriv t x] using hd.hasDerivAt
  have hprofile := (P.profile_hasDerivAt (ExplicitSolution.endpointScale t x)).comp t hscale
  have hprofileDeriv :
      deriv (fun τ : ℝ => P.profile (ExplicitSolution.endpointScale τ x)) t =
        P.profileFirst (ExplicitSolution.endpointScale t x) *
          (-x * deriv TimeScaling.ySym t / (TimeScaling.ySym t)^2) := by
    simpa [Function.comp_def] using hprofile.deriv
  have hprofileDiff : DifferentiableAt ℝ
      (fun τ : ℝ => P.profile (ExplicitSolution.endpointScale τ x)) t := by
    simpa [Function.comp_def] using hprofile.differentiableAt
  unfold compactAmplitude
  rw [deriv_fun_mul hwidth hprofileDiff]
  rw [ExplicitSolution.endpointWidthFactor_t_deriv, hprofileDeriv]
  ring

/-- NODE HE.CompactSupportConstruction.complex_phase_factor_deriv
deps:
statement: differentiate a complex exponential of a differentiable real phase.
-/
lemma complexPhaseFactor_hasDerivAt (phi : ℝ → ℝ) (phi' x : ℝ)
    (hphi : HasDerivAt phi phi' x) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (phi y : ℂ)))
      (Complex.exp (Complex.I * (phi x : ℂ)) *
        (Complex.I * (phi' : ℂ))) x := by
  have hreal : HasDerivAt (fun y : ℝ => (phi y : ℂ)) (phi' : ℂ) x :=
    hphi.ofReal_comp
  have hinner := hreal.const_mul Complex.I
  simpa using hinner.cexp

/-- NODE HE.CompactSupportConstruction.complex_amplitude_phase_deriv
deps: HE.CompactSupportConstruction.complex_phase_factor_deriv
statement: differentiate a real amplitude multiplied by a complex real-phase exponential.
-/
lemma complexAmplitudePhase_hasDerivAt
    (amp phase : ℝ → ℝ) (amp' phase' x : ℝ)
    (hamp : HasDerivAt amp amp' x) (hphase : HasDerivAt phase phase' x) :
    HasDerivAt
      (fun y : ℝ => (amp y : ℂ) *
        Complex.exp (Complex.I * (phase y : ℂ)))
      ((amp' : ℂ) * Complex.exp (Complex.I * (phase x : ℂ)) +
        (amp x : ℂ) *
          (Complex.exp (Complex.I * (phase x : ℂ)) *
            (Complex.I * (phase' : ℂ)))) x := by
  exact hamp.ofReal_comp.mul (complexPhaseFactor_hasDerivAt phase phase' x hphase)

lemma compactAmplitude_differentiableAt_t
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ (fun τ : ℝ => compactAmplitude P τ x) t := by
  have hy : TimeScaling.ySym t ≠ 0 := TimeScaling.symmetric_y_ne_zero t
  have hsqrt : Real.sqrt (TimeScaling.ySym t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (TimeScaling.symmetric_y_pos t))
  have hwidth : DifferentiableAt ℝ
      (fun τ : ℝ => 1 / Real.sqrt (TimeScaling.ySym τ)) t :=
    (differentiableAt_const (1 : ℝ)).div
      ((TimeScaling.ySym_hasDerivAt t).differentiableAt.sqrt hy) hsqrt
  have hscale := ExplicitSolution.endpointScale_differentiableAt_t t x
  have hprofile :=
    (P.profile_hasDerivAt (ExplicitSolution.endpointScale t x)).differentiableAt.comp t hscale
  unfold compactAmplitude
  exact hwidth.mul hprofile

lemma compactPhase_differentiableAt_t
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ (fun τ : ℝ => compactPhase P τ x) t := by
  unfold compactPhase
  exact ((ExplicitSolution.endpointB_differentiableAt t).mul (differentiableAt_const _)).add
    (((show DifferentiableAt ℝ (fun τ : ℝ => 2 * τ - 1) t from by
      fun_prop).arctan).const_mul (P.remainderInf / 4))

/-- NODE HE.CompactSupportConstruction.compact_solution_t_deriv
deps: HE.CompactSupportConstruction.complex_amplitude_phase_deriv, HE.CompactSupportConstruction.compact_amplitude_t_deriv, HE.CompactSupportConstruction.compact_phase_t_deriv
statement: express the time derivative of the compact complex candidate through its real amplitude and phase derivatives.
-/
lemma compactSolution_t_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun τ : ℝ => compactSolution P τ x) t =
      ((deriv (fun τ : ℝ => compactAmplitude P τ x) t : ℝ) : ℂ) *
          Complex.exp (Complex.I * (compactPhase P t x : ℂ)) +
        (compactAmplitude P t x : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
            (Complex.I *
              ((deriv (fun τ : ℝ => compactPhase P τ x) t : ℝ) : ℂ))) := by
  have hamp := (compactAmplitude_differentiableAt_t P t x).hasDerivAt
  have hphase := (compactPhase_differentiableAt_t P t x).hasDerivAt
  unfold compactSolution
  exact (complexAmplitudePhase_hasDerivAt
    (fun τ : ℝ => compactAmplitude P τ x)
    (fun τ : ℝ => compactPhase P τ x)
    (deriv (fun τ : ℝ => compactAmplitude P τ x) t)
    (deriv (fun τ : ℝ => compactPhase P τ x) t)
    t hamp hphase).deriv

lemma compactAmplitude_differentiableAt_x
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ (fun ξ : ℝ => compactAmplitude P t ξ) x := by
  have hscale : DifferentiableAt ℝ
      (fun ξ : ℝ => ExplicitSolution.endpointScale t ξ) x := by
    unfold ExplicitSolution.endpointScale
    fun_prop
  have hprofile :=
    (P.profile_hasDerivAt (ExplicitSolution.endpointScale t x)).differentiableAt.comp x hscale
  unfold compactAmplitude
  exact (differentiableAt_const (1 / Real.sqrt (TimeScaling.ySym t))).mul hprofile

lemma compactPhase_differentiableAt_x
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ (fun ξ : ℝ => compactPhase P t ξ) x := by
  unfold compactPhase
  fun_prop

/-- NODE HE.CompactSupportConstruction.compact_solution_x_deriv
deps: HE.CompactSupportConstruction.complex_amplitude_phase_deriv, HE.CompactSupportConstruction.compact_amplitude_x_deriv, HE.CompactSupportConstruction.compact_phase_x_deriv
statement: express the first spatial derivative of the compact complex candidate through its amplitude and phase derivatives.
-/
lemma compactSolution_x_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (fun ξ : ℝ => compactSolution P t ξ) x =
      ((deriv (fun ξ : ℝ => compactAmplitude P t ξ) x : ℝ) : ℂ) *
          Complex.exp (Complex.I * (compactPhase P t x : ℂ)) +
        (compactAmplitude P t x : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
            (Complex.I *
              ((deriv (fun ξ : ℝ => compactPhase P t ξ) x : ℝ) : ℂ))) := by
  have hamp := (compactAmplitude_differentiableAt_x P t x).hasDerivAt
  have hphase := (compactPhase_differentiableAt_x P t x).hasDerivAt
  unfold compactSolution
  exact (complexAmplitudePhase_hasDerivAt
    (fun ξ : ℝ => compactAmplitude P t ξ)
    (fun ξ : ℝ => compactPhase P t ξ)
    (deriv (fun ξ : ℝ => compactAmplitude P t ξ) x)
    (deriv (fun ξ : ℝ => compactPhase P t ξ) x)
    x hamp hphase).deriv

lemma compactAmplitude_x_deriv_differentiableAt
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ
      (fun η : ℝ => deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) x := by
  have hfun : (fun η : ℝ => deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) =
      fun η : ℝ => (1 / Real.sqrt (TimeScaling.ySym t)) *
        P.profileFirst (ExplicitSolution.endpointScale t η) / TimeScaling.ySym t := by
    funext η
    exact compactAmplitude_x_deriv P t η
  rw [hfun]
  have hscale : DifferentiableAt ℝ (fun η : ℝ => ExplicitSolution.endpointScale t η) x := by
    unfold ExplicitSolution.endpointScale
    fun_prop
  have hp :=
    (P.profileFirst_hasDerivAt (ExplicitSolution.endpointScale t x)).differentiableAt.comp x hscale
  exact ((differentiableAt_const _).mul hp).div_const _

lemma compactPhase_x_deriv_differentiableAt
    (P : CompactProfileData) (t x : ℝ) :
    DifferentiableAt ℝ
      (fun η : ℝ => deriv (fun ξ : ℝ => compactPhase P t ξ) η) x := by
  have hfun : (fun η : ℝ => deriv (fun ξ : ℝ => compactPhase P t ξ) η) =
      fun η : ℝ => 2 * ExplicitSolution.endpointB t * η := by
    funext η
    exact compactPhase_x_deriv P t η
  rw [hfun]
  fun_prop

/-- NODE HE.CompactSupportConstruction.compact_solution_x_second_deriv
deps: HE.CompactSupportConstruction.compact_solution_x_deriv, HE.CompactSupportConstruction.compact_amplitude_x_second_deriv, HE.CompactSupportConstruction.compact_phase_x_second_deriv
statement: express the second spatial derivative of the compact complex candidate through amplitude and phase derivatives.
-/
lemma compactSolution_x_second_deriv (P : CompactProfileData) (t x : ℝ) :
    deriv (deriv (fun ξ : ℝ => compactSolution P t ξ)) x =
      ((deriv (fun η : ℝ => deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) x : ℝ) : ℂ) *
          Complex.exp (Complex.I * (compactPhase P t x : ℂ)) +
        ((deriv (fun ξ : ℝ => compactAmplitude P t ξ) x : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
            (Complex.I * ((deriv (fun ξ : ℝ => compactPhase P t ξ) x : ℝ) : ℂ))) +
        ((deriv (fun ξ : ℝ => compactAmplitude P t ξ) x : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
            (Complex.I * ((deriv (fun ξ : ℝ => compactPhase P t ξ) x : ℝ) : ℂ))) +
        (compactAmplitude P t x : ℂ) *
          (((Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
              (Complex.I * ((deriv (fun ξ : ℝ => compactPhase P t ξ) x : ℝ) : ℂ))) *
            (Complex.I * ((deriv (fun ξ : ℝ => compactPhase P t ξ) x : ℝ) : ℂ))) +
            Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
              (Complex.I *
                ((deriv (fun η : ℝ => deriv (fun ξ : ℝ => compactPhase P t ξ) η) x : ℝ) : ℂ))) := by
  have hfun : deriv (fun ξ : ℝ => compactSolution P t ξ) = fun η : ℝ =>
      ((deriv (fun ξ : ℝ => compactAmplitude P t ξ) η : ℝ) : ℂ) *
          Complex.exp (Complex.I * (compactPhase P t η : ℂ)) +
        (compactAmplitude P t η : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t η : ℂ)) *
            (Complex.I * ((deriv (fun ξ : ℝ => compactPhase P t ξ) η : ℝ) : ℂ))) := by
    funext η
    exact compactSolution_x_deriv P t η
  rw [hfun]
  have ha := (compactAmplitude_differentiableAt_x P t x).hasDerivAt
  have hap := (compactAmplitude_x_deriv_differentiableAt P t x).hasDerivAt
  have hp := (compactPhase_differentiableAt_x P t x).hasDerivAt
  have hpp := (compactPhase_x_deriv_differentiableAt P t x).hasDerivAt
  have hE := complexPhaseFactor_hasDerivAt
    (fun ξ : ℝ => compactPhase P t ξ)
    (deriv (fun ξ : ℝ => compactPhase P t ξ) x) x hp
  have hIp := hpp.ofReal_comp.const_mul Complex.I
  have htotal := hap.ofReal_comp.mul hE |>.add
    (ha.ofReal_comp.mul (hE.mul hIp))
  change HasDerivAt (fun η : ℝ =>
      ((deriv (fun ξ : ℝ => compactAmplitude P t ξ) η : ℝ) : ℂ) *
          Complex.exp (Complex.I * (compactPhase P t η : ℂ)) +
        (compactAmplitude P t η : ℂ) *
          (Complex.exp (Complex.I * (compactPhase P t η : ℂ)) *
            (Complex.I *
              ((deriv (fun ξ : ℝ => compactPhase P t ξ) η : ℝ) : ℂ)))) _ x at htotal
  have hv := htotal.deriv
  simp only [Pi.mul_apply] at hv
  convert hv using 1 <;> ring

/-- NODE HE.CompactSupportConstruction.compact_residual_decomposition
deps: HE.CompactSupportConstruction.compact_solution_t_deriv, HE.CompactSupportConstruction.compact_solution_x_second_deriv
statement: split the compact Schrodinger residual into real and imaginary scalar brackets.
-/
lemma compactResidual_decomposition (P : CompactProfileData) (t x : ℝ) :
    let realPart : ℝ :=
      deriv (fun η : ℝ =>
          deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) x -
        compactAmplitude P t x * deriv (fun τ : ℝ => compactPhase P τ x) t -
        compactAmplitude P t x * (deriv (fun ξ : ℝ => compactPhase P t ξ) x)^2 -
        compactPotential P t x * compactAmplitude P t x
    let imagPart : ℝ :=
      deriv (fun τ : ℝ => compactAmplitude P τ x) t +
        2 * deriv (fun ξ : ℝ => compactPhase P t ξ) x *
          deriv (fun ξ : ℝ => compactAmplitude P t ξ) x +
        deriv (fun η : ℝ =>
          deriv (fun ξ : ℝ => compactPhase P t ξ) η) x * compactAmplitude P t x
    Complex.I * deriv (fun τ : ℝ => compactSolution P τ x) t +
        deriv (deriv (fun ξ : ℝ => compactSolution P t ξ)) x -
          (compactPotential P t x : ℂ) * compactSolution P t x =
      Complex.exp (Complex.I * (compactPhase P t x : ℂ)) *
        ((realPart : ℂ) + Complex.I * (imagPart : ℂ)) := by
  dsimp only
  rw [compactSolution_t_deriv, compactSolution_x_second_deriv]
  unfold compactSolution
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- NODE HE.CompactSupportConstruction.compact_residual_imaginary
deps: HE.CompactSupportConstruction.compact_amplitude_t_deriv, HE.CompactSupportConstruction.compact_amplitude_x_deriv, HE.CompactSupportConstruction.compact_phase_x_deriv, HE.CompactSupportConstruction.compact_phase_x_second_deriv
statement: the imaginary transport bracket in the compact residual vanishes.
-/
lemma compactResidual_imaginary (P : CompactProfileData) (t x : ℝ) :
    deriv (fun τ : ℝ => compactAmplitude P τ x) t +
        2 * deriv (fun ξ : ℝ => compactPhase P t ξ) x *
          deriv (fun ξ : ℝ => compactAmplitude P t ξ) x +
        deriv (fun η : ℝ =>
          deriv (fun ξ : ℝ => compactPhase P t ξ) η) x *
            compactAmplitude P t x = 0 := by
  rw [compactAmplitude_t_deriv, compactPhase_x_deriv,
    compactAmplitude_x_deriv]
  have hphaseX : 2 * ExplicitSolution.endpointB t * x =
      ExplicitSolution.endpointScale t x * deriv TimeScaling.ySym t / 2 := by
    calc
      2 * ExplicitSolution.endpointB t * x =
          ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x := by
            unfold ExplicitSolution.endpointB
            field_simp [TimeScaling.symmetric_q_ne_zero t]
            ring
      _ = _ := ExplicitSolution.phase_x_width_form t x
  have hphaseXX : 2 * ExplicitSolution.endpointB t =
      deriv TimeScaling.ySym t / (2 * TimeScaling.ySym t) := by
    calc
      2 * ExplicitSolution.endpointB t =
          (2 * t - 1) / (2 * TimeScaling.qSym t) := by
            unfold ExplicitSolution.endpointB
            field_simp [TimeScaling.symmetric_q_ne_zero t]
            ring
      _ = _ := ExplicitSolution.phase_xx_width_form t
  have hsecond : deriv (fun η : ℝ =>
      deriv (fun ξ : ℝ => compactPhase P t ξ) η) x =
        2 * ExplicitSolution.endpointB t := by
    simpa using compactPhase_x_second_deriv P t x
  rw [hsecond, hphaseX, hphaseXX]
  unfold compactAmplitude ExplicitSolution.endpointScale
  have hy := TimeScaling.symmetric_y_ne_zero t
  field_simp [hy]
  ring

/-- NODE HE.CompactSupportConstruction.compact_residual_real
deps: HE.CompactSupportConstruction.compact_amplitude_x_second_deriv, HE.CompactSupportConstruction.compact_phase_t_deriv, HE.CompactSupportConstruction.compact_phase_x_deriv
statement: the real elliptic and phase-energy bracket in the compact residual vanishes.
-/
lemma compactResidual_real (P : CompactProfileData) (t x : ℝ) :
    deriv (fun η : ℝ =>
          deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) x -
        compactAmplitude P t x * deriv (fun τ : ℝ => compactPhase P τ x) t -
        compactAmplitude P t x *
          (deriv (fun ξ : ℝ => compactPhase P t ξ) x)^2 -
        compactPotential P t x * compactAmplitude P t x = 0 := by
  have hsecond : deriv (fun η : ℝ =>
      deriv (fun ξ : ℝ => compactAmplitude P t ξ) η) x =
        (1 / Real.sqrt (TimeScaling.ySym t)) *
          P.profileSecond (ExplicitSolution.endpointScale t x) /
            (TimeScaling.ySym t)^2 := by
    simpa using compactAmplitude_x_second_deriv P t x
  rw [hsecond, compactPhase_t_deriv, compactPhase_x_deriv]
  have hphaseX : 2 * ExplicitSolution.endpointB t * x =
      ((2 * t - 1) / (2 * TimeScaling.qSym t)) * x := by
    unfold ExplicitSolution.endpointB
    field_simp [TimeScaling.symmetric_q_ne_zero t]
    ring
  rw [hphaseX]
  have hphase := ExplicitSolution.phase_energy_width_identity t x
  have hySq : (TimeScaling.ySym t)^2 = 4 * TimeScaling.qSym t :=
    TimeScaling.symmetric_y_sq t
  have henergy :
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          P.remainderInf / (4 * TimeScaling.qSym t) +
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 =
      (4 * (ExplicitSolution.endpointScale t x)^2 + P.remainderInf) /
        (TimeScaling.ySym t)^2 := by
    have hq := TimeScaling.symmetric_q_ne_zero t
    have hy := TimeScaling.symmetric_y_ne_zero t
    unfold ExplicitSolution.endpointScale at hphase ⊢
    field_simp [hq, hy]
    have hy4 : (TimeScaling.ySym t)^4 =
        (4 * TimeScaling.qSym t)^2 := by nlinarith [hySq]
    rw [hy4, hySq]
    ring
  have hprofile := P.oscillator_identity (ExplicitSolution.endpointScale t x)
  have henergy' :
      (t * (1 - t) / (TimeScaling.qSym t)^2) * x^2 +
          P.remainderInf / (4 * TimeScaling.qSym t) =
      (4 * (ExplicitSolution.endpointScale t x)^2 + P.remainderInf) /
          (TimeScaling.ySym t)^2 -
        (((2 * t - 1) / (2 * TimeScaling.qSym t)) * x)^2 := by
    linarith [henergy]
  unfold compactAmplitude compactPotential
  rw [henergy']
  rw [hprofile]
  have hy := TimeScaling.symmetric_y_ne_zero t
  field_simp [hy]
  ring

/-! ## Schrödinger equation, boundedness, support, and endpoint decay -/

/-- NODE HE.CompactSupportConstruction.candidate_schrodinger
deps: HE.CompactSupportConstruction.profile_data_exists, HE.CompactSupportConstruction.compact_residual_decomposition, HE.CompactSupportConstruction.compact_residual_imaginary, HE.CompactSupportConstruction.compact_residual_real
statement: the candidate pair satisfies the one-dimensional Schrodinger equation pointwise.
-/
theorem compactCandidate_schrodinger :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      Complex.I * deriv
          (fun τ : ℝ => compactSolution compactProfileData τ x) t +
          deriv (deriv
            (fun ξ : ℝ => compactSolution compactProfileData t ξ)) x =
        (compactPotential compactProfileData t x : ℂ) *
          compactSolution compactProfileData t x := by
  intro t _ x
  apply sub_eq_zero.mp
  rw [compactResidual_decomposition]
  rw [compactResidual_real, compactResidual_imaginary]
  simp

end CompactSupportConstruction
end HardyCompactSupport

