import HardyCompactSupport.GaussianTailProfile

/-!
# Positive glued profile
-/

noncomputable section

namespace HardyCompactSupport
namespace CompactSupportConstruction

open intervalIntegral
open Filter
open scoped ContDiff

/-! ## Smooth gluing across the compact transition region -/

/-- Smooth switch selecting the right exterior profile. -/
def rightGluingCutoff (x : ℝ) : ℝ := Real.smoothTransition (x - 1)

/-- Smooth switch selecting the reflected left exterior profile. -/
def leftGluingCutoff (x : ℝ) : ℝ := Real.smoothTransition (-x - 1)

/-- NODE HE.CompactSupportConstruction.gluing_cutoffs_smooth
deps:
statement: both exterior gluing switches are infinitely differentiable.
-/
theorem gluingCutoffs_smooth :
    ContDiff ℝ ∞ rightGluingCutoff ∧ ContDiff ℝ ∞ leftGluingCutoff := by
  have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  constructor
  · unfold rightGluingCutoff
    have hinner : ContDiff ℝ ∞ (fun x : ℝ => x - 1) := by fun_prop
    exact hsmooth.comp hinner
  · unfold leftGluingCutoff
    have hinner : ContDiff ℝ ∞ (fun x : ℝ => -x - 1) := by fun_prop
    exact hsmooth.comp hinner

/-- NODE HE.CompactSupportConstruction.right_gluing_cutoff_values
deps:
statement: the right switch is zero on the interior side and one on the far exterior.
-/
theorem rightGluingCutoff_values (x : ℝ) :
    (x ≤ 1 → rightGluingCutoff x = 0) ∧
      (2 ≤ x → rightGluingCutoff x = 1) := by
  constructor
  · intro hx
    unfold rightGluingCutoff
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · intro hx
    unfold rightGluingCutoff
    exact Real.smoothTransition.one_of_one_le (by linarith)

/-- NODE HE.CompactSupportConstruction.left_gluing_cutoff_values
deps:
statement: the left switch is zero on the interior side and one on the far exterior.
-/
theorem leftGluingCutoff_values (x : ℝ) :
    (-1 ≤ x → leftGluingCutoff x = 0) ∧
      (x ≤ -2 → leftGluingCutoff x = 1) := by
  constructor
  · intro hx
    unfold leftGluingCutoff
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · intro hx
    unfold leftGluingCutoff
    exact Real.smoothTransition.one_of_one_le (by linarith)

/-- NODE HE.CompactSupportConstruction.gluing_cutoff_bounds
deps:
statement: both gluing switches take values in the closed unit interval.
-/
theorem gluingCutoff_bounds (x : ℝ) :
    0 ≤ rightGluingCutoff x ∧ rightGluingCutoff x ≤ 1 ∧
      0 ≤ leftGluingCutoff x ∧ leftGluingCutoff x ≤ 1 := by
  unfold rightGluingCutoff leftGluingCutoff
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _,
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The global profile obtained by smoothly selecting the two exterior modes
and the constant positive interior profile. -/
def gluedProfile (x : ℝ) : ℝ :=
  1 + rightGluingCutoff x *
      (exteriorMasterProfile gaussianHalfMass x - 1) +
    leftGluingCutoff x *
      (exteriorMasterProfile gaussianHalfMass (-x) - 1)

/-- NODE HE.CompactSupportConstruction.glued_profile_smooth
deps: HE.CompactSupportConstruction.gluing_cutoffs_smooth, HE.CompactSupportConstruction.exterior_master_smooth
statement: the globally glued profile is infinitely differentiable.
-/
lemma gluedProfile_smooth : ContDiff ℝ ∞ gluedProfile := by
  have hright := gluingCutoffs_smooth.1
  have hleft := gluingCutoffs_smooth.2
  have hF := exteriorMasterProfile_smooth gaussianHalfMass
  have hFneg : ContDiff ℝ ∞
      (fun x : ℝ => exteriorMasterProfile gaussianHalfMass (-x)) :=
    hF.comp (by fun_prop)
  unfold gluedProfile
  exact (contDiff_const.add (hright.mul (hF.sub contDiff_const))).add
    (hleft.mul (hFneg.sub contDiff_const))

/-- NODE HE.CompactSupportConstruction.glued_profile_center_value
deps: HE.CompactSupportConstruction.right_gluing_cutoff_values, HE.CompactSupportConstruction.left_gluing_cutoff_values
statement: the glued profile equals one at the origin.
-/
lemma gluedProfile_zero : gluedProfile 0 = 1 := by
  unfold gluedProfile
  rw [show rightGluingCutoff 0 = 0 from (rightGluingCutoff_values 0).1 (by norm_num)]
  rw [show leftGluingCutoff 0 = 0 from (leftGluingCutoff_values 0).1 (by norm_num)]
  simp

/-- NODE HE.CompactSupportConstruction.glued_profile_right_exterior
deps: HE.CompactSupportConstruction.right_gluing_cutoff_values, HE.CompactSupportConstruction.left_gluing_cutoff_values
statement: on the far right, the glued profile is exactly the distinguished exterior mode.
-/
lemma gluedProfile_eq_right {x : ℝ} (hx : 2 ≤ x) :
    gluedProfile x = exteriorMasterProfile gaussianHalfMass x := by
  have hr := (rightGluingCutoff_values x).2 hx
  have hl := (leftGluingCutoff_values x).1 (by linarith)
  unfold gluedProfile
  rw [hr, hl]
  ring

/-- NODE HE.CompactSupportConstruction.glued_profile_left_exterior
deps: HE.CompactSupportConstruction.right_gluing_cutoff_values, HE.CompactSupportConstruction.left_gluing_cutoff_values
statement: on the far left, the glued profile is the reflected distinguished exterior mode.
-/
lemma gluedProfile_eq_left {x : ℝ} (hx : x ≤ -2) :
    gluedProfile x = exteriorMasterProfile gaussianHalfMass (-x) := by
  have hr := (rightGluingCutoff_values x).1 (by linarith)
  have hl := (leftGluingCutoff_values x).2 hx
  unfold gluedProfile
  rw [hr, hl]
  ring

lemma convexBlend_pos {theta a : ℝ} (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (ha : 0 < a) :
    0 < 1 + theta * (a - 1) := by
  have hfirst : 0 ≤ 1 - theta := sub_nonneg.2 htheta1
  by_cases htheta : theta = 0
  · simp [htheta]
  · have hthetaPos : 0 < theta := lt_of_le_of_ne htheta0 (Ne.symm htheta)
    calc
      1 + theta * (a - 1) = (1 - theta) + theta * a := by ring
      _ > 0 := add_pos_of_nonneg_of_pos hfirst (mul_pos hthetaPos ha)

/-- NODE HE.CompactSupportConstruction.glued_profile_positive
deps: HE.CompactSupportConstruction.gluing_cutoff_bounds, HE.CompactSupportConstruction.right_gluing_cutoff_values, HE.CompactSupportConstruction.left_gluing_cutoff_values, HE.CompactSupportConstruction.distinguished_exterior_master_positive
statement: the smoothly glued global profile is strictly positive everywhere.
-/
lemma gluedProfile_pos (x : ℝ) : 0 < gluedProfile x := by
  by_cases hright : 1 < x
  · have hleftZero := (leftGluingCutoff_values x).1 (by linarith)
    have hbounds := gluingCutoff_bounds x
    unfold gluedProfile
    rw [hleftZero]
    simp only [zero_mul, add_zero]
    exact convexBlend_pos hbounds.1 hbounds.2.1
      (exteriorMasterProfile_halfMass_pos (by linarith))
  · have hxle : x ≤ 1 := le_of_not_gt hright
    by_cases hleft : x < -1
    · have hrightZero := (rightGluingCutoff_values x).1 hxle
      have hbounds := gluingCutoff_bounds x
      unfold gluedProfile
      rw [hrightZero]
      simp only [zero_mul, add_zero]
      exact convexBlend_pos hbounds.2.2.1 hbounds.2.2.2
        (exteriorMasterProfile_halfMass_pos (by linarith))
    · have hxge : -1 ≤ x := le_of_not_gt hleft
      have hrightZero := (rightGluingCutoff_values x).1 hxle
      have hleftZero := (leftGluingCutoff_values x).1 hxge
      unfold gluedProfile
      rw [hrightZero, hleftZero]
      norm_num

/-! ## Eventually constant remainder and boundedness -/

/-- The first derivative field of the glued profile. -/
def gluedProfileFirst (x : ℝ) : ℝ := deriv gluedProfile x

/-- The second derivative field of the glued profile. -/
def gluedProfileSecond (x : ℝ) : ℝ := deriv (deriv gluedProfile) x

/-- The master remainder induced by the positive glued profile. -/
def gluedRemainder (x : ℝ) : ℝ :=
  gluedProfileSecond x / gluedProfile x - 4 * x^2

/-- NODE HE.CompactSupportConstruction.glued_profile_derivative_data
deps: HE.CompactSupportConstruction.glued_profile_smooth
statement: the named first and second derivative fields are the pointwise derivatives of the glued profile.
-/
theorem gluedProfile_derivative_data (x : ℝ) :
    HasDerivAt gluedProfile (gluedProfileFirst x) x ∧
      HasDerivAt gluedProfileFirst (gluedProfileSecond x) x := by
  have hfirstSmooth : ContDiff ℝ ∞ (deriv gluedProfile) :=
    (contDiff_infty_iff_deriv.mp gluedProfile_smooth).2
  constructor
  · exact (gluedProfile_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  · unfold gluedProfileFirst gluedProfileSecond
    exact (hfirstSmooth.differentiable (by simp)).differentiableAt.hasDerivAt

/-- NODE HE.CompactSupportConstruction.glued_remainder_smooth
deps: HE.CompactSupportConstruction.glued_profile_smooth, HE.CompactSupportConstruction.glued_profile_positive
statement: the quotient-defined master remainder is infinitely differentiable.
-/
lemma gluedRemainder_smooth : ContDiff ℝ ∞ gluedRemainder := by
  have hfirstSmooth : ContDiff ℝ ∞ (deriv gluedProfile) :=
    (contDiff_infty_iff_deriv.mp gluedProfile_smooth).2
  have hsecondSmooth : ContDiff ℝ ∞ (deriv (deriv gluedProfile)) :=
    (contDiff_infty_iff_deriv.mp hfirstSmooth).2
  unfold gluedRemainder gluedProfileSecond
  exact (hsecondSmooth.div gluedProfile_smooth
    (fun x => (gluedProfile_pos x).ne')).sub (by fun_prop)

/-- NODE HE.CompactSupportConstruction.glued_oscillator_identity
deps: HE.CompactSupportConstruction.glued_profile_positive
statement: the glued profile satisfies the master oscillator equation with its induced remainder.
-/
lemma gluedProfile_oscillator_identity (x : ℝ) :
    gluedProfileSecond x =
      (4 * x^2 + gluedRemainder x) * gluedProfile x := by
  unfold gluedRemainder
  field_simp [(gluedProfile_pos x).ne']
  ring

/-- NODE HE.CompactSupportConstruction.reflected_exterior_master_ode
deps: HE.CompactSupportConstruction.exterior_master_first_derivative, HE.CompactSupportConstruction.exterior_master_second_derivative
statement: reflecting the distinguished exterior profile preserves its second-order oscillator equation.
-/
lemma reflectedExteriorMaster_ode (C x : ℝ) :
    deriv (deriv (fun y : ℝ => exteriorMasterProfile C (-y))) x =
      (4 * x^2 + 2) * exteriorMasterProfile C (-x) := by
  have hneg (y : ℝ) : HasDerivAt (fun z : ℝ => -z) (-1) y := by
    have hraw := (hasDerivAt_id y).const_mul (-1)
    convert hraw using 1 <;> first | rfl | simp | ring
  have hfirstDeriv (y : ℝ) :
      deriv (fun z : ℝ => exteriorMasterProfile C (-z)) y =
        -exteriorMasterFirst C (-y) := by
    have h := (exteriorMasterProfile_hasDerivAt C (-y)).comp y (hneg y)
    have h' : HasDerivAt (fun z : ℝ => exteriorMasterProfile C (-z))
        (-exteriorMasterFirst C (-y)) y := by
      convert h using 1 <;> first | rfl | simp [Function.comp_def] | ring
    exact h'.deriv
  have hfirstFun : deriv (fun y : ℝ => exteriorMasterProfile C (-y)) =
      fun y : ℝ => -exteriorMasterFirst C (-y) := by
    funext y
    exact hfirstDeriv y
  rw [hfirstFun]
  have h := (exteriorMasterFirst_hasDerivAt C (-x)).comp x (hneg x)
  have htotal := h.neg
  have htotal' : HasDerivAt (fun y : ℝ => -exteriorMasterFirst C (-y))
      ((4 * x^2 + 2) * exteriorMasterProfile C (-x)) x := by
    convert htotal using 1 <;> first | rfl | simp [Function.comp_def] | ring
  exact htotal'.deriv

/-- NODE HE.CompactSupportConstruction.glued_remainder_right_exterior
deps: HE.CompactSupportConstruction.glued_profile_right_exterior, HE.CompactSupportConstruction.exterior_master_ode
statement: the induced master remainder equals two strictly beyond the right gluing boundary.
-/
lemma gluedRemainder_eq_right {x : ℝ} (hx : 2 < x) : gluedRemainder x = 2 := by
  have heq : gluedProfile =ᶠ[nhds x]
      exteriorMasterProfile gaussianHalfMass := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact gluedProfile_eq_right (le_of_lt hy)
  have hsecond : gluedProfileSecond x =
      deriv (deriv (exteriorMasterProfile gaussianHalfMass)) x := by
    unfold gluedProfileSecond
    exact (heq.deriv).deriv_eq
  unfold gluedRemainder
  rw [hsecond, exteriorMasterProfile_ode]
  rw [gluedProfile_eq_right (le_of_lt hx)]
  have hpos : 0 < exteriorMasterProfile gaussianHalfMass x :=
    exteriorMasterProfile_halfMass_pos (by linarith)
  have hne : exteriorMasterProfile gaussianHalfMass x ≠ 0 := hpos.ne'
  field_simp [hne]
  ring

/-- NODE HE.CompactSupportConstruction.glued_remainder_left_exterior
deps: HE.CompactSupportConstruction.glued_profile_left_exterior, HE.CompactSupportConstruction.reflected_exterior_master_ode
statement: the induced master remainder equals two strictly beyond the left gluing boundary.
-/
lemma gluedRemainder_eq_left {x : ℝ} (hx : x < -2) : gluedRemainder x = 2 := by
  let reflected : ℝ → ℝ := fun y => exteriorMasterProfile gaussianHalfMass (-y)
  have heq : gluedProfile =ᶠ[nhds x] reflected := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact gluedProfile_eq_left (le_of_lt hy)
  have hsecond : gluedProfileSecond x = deriv (deriv reflected) x := by
    unfold gluedProfileSecond
    exact (heq.deriv).deriv_eq
  unfold gluedRemainder
  rw [hsecond]
  change deriv (deriv (fun y : ℝ =>
    exteriorMasterProfile gaussianHalfMass (-y))) x / gluedProfile x - 4 * x^2 = 2
  rw [reflectedExteriorMaster_ode]
  rw [gluedProfile_eq_left (le_of_lt hx)]
  have hpos : 0 < exteriorMasterProfile gaussianHalfMass (-x) :=
    exteriorMasterProfile_halfMass_pos (by linarith)
  have hne : exteriorMasterProfile gaussianHalfMass (-x) ≠ 0 := hpos.ne'
  field_simp [hne]
  ring

/-- NODE HE.CompactSupportConstruction.glued_remainder_exterior
deps: HE.CompactSupportConstruction.glued_remainder_right_exterior, HE.CompactSupportConstruction.glued_remainder_left_exterior
statement: the induced master remainder is the constant two outside radius three.
-/
lemma gluedRemainder_exterior (x : ℝ) (hx : (3 : ℝ) ≤ |x|) :
    gluedRemainder x = 2 := by
  rcases le_total 0 x with hnonneg | hnonpos
  · apply gluedRemainder_eq_right
    rw [abs_of_nonneg hnonneg] at hx
    linarith
  · apply gluedRemainder_eq_left
    rw [abs_of_nonpos hnonpos] at hx
    linarith

/-- NODE HE.CompactSupportConstruction.glued_remainder_bounded
deps: HE.CompactSupportConstruction.glued_remainder_smooth, HE.CompactSupportConstruction.glued_remainder_exterior
statement: the compactly perturbed master remainder differs from two by a global finite bound.
-/
lemma gluedRemainder_bounded_exists :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |gluedRemainder x - 2| ≤ B := by
  have hcont : ContinuousOn (fun x : ℝ => |gluedRemainder x - 2|)
      (Set.Icc (-3 : ℝ) 3) :=
    (gluedRemainder_smooth.continuous.sub continuous_const).abs.continuousOn
  have hbdd : BddAbove
      ((fun x : ℝ => |gluedRemainder x - 2|) '' Set.Icc (-3 : ℝ) 3) :=
    isCompact_Icc.bddAbove_image hcont
  rcases hbdd with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ Set.Icc (-3 : ℝ) 3
  · exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · have hxout : x < -3 ∨ 3 < x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      exact hx
    have habs : (3 : ℝ) ≤ |x| := by
      rcases hxout with hleft | hright
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    rw [gluedRemainder_exterior x habs]
    simp [le_max_right B 0]

/-! ## Critical weighted integrability of the glued profile -/

/-- The critical weighted square whose integrability is required at both endpoints. -/
def gluedWeightedSquare (x : ℝ) : ℝ :=
  (Real.exp (x^2) * gluedProfile x)^2

lemma gluedWeightedSquare_continuous : Continuous gluedWeightedSquare := by
  unfold gluedWeightedSquare
  have hExp : Continuous (fun x : ℝ => Real.exp (x^2)) := by fun_prop
  exact (hExp.mul gluedProfile_smooth.continuous).pow 2

/-- NODE HE.CompactSupportConstruction.glued_weighted_square_right_bound
deps: HE.CompactSupportConstruction.glued_profile_right_exterior, HE.CompactSupportConstruction.critical_weight_cancels_exterior_gaussian, HE.CompactSupportConstruction.distinguished_exterior_profile_positive, HE.CompactSupportConstruction.distinguished_exterior_profile_mills_bound
statement: on the right tail, the critical weighted square is dominated by the standard integrable rational tail.
-/
lemma gluedWeightedSquare_right_bound {x : ℝ} (hx : 2 < x) :
    gluedWeightedSquare x ≤ 1 / (1 + x^2) := by
  have hweighted : Real.exp (x^2) * gluedProfile x =
      exteriorProfile gaussianHalfMass x := by
    rw [gluedProfile_eq_right (le_of_lt hx)]
    exact weightedExteriorMaster_eq gaussianHalfMass x
  rw [gluedWeightedSquare, hweighted]
  have hpos := exteriorProfile_halfMass_pos (by linarith : 0 ≤ x)
  have hle := exteriorProfile_halfMass_le (by linarith : 0 < x)
  have hrecip : 0 ≤ 1 / (4 * x) := by positivity
  have hsquare : (exteriorProfile gaussianHalfMass x)^2 ≤ (1 / (4 * x))^2 := by
    nlinarith
  calc
    (exteriorProfile gaussianHalfMass x)^2 ≤ (1 / (4 * x))^2 := hsquare
    _ ≤ 1 / (1 + x^2) := by
      have hdenPos : 0 < 1 + x^2 := by positivity
      have hden : 1 + x^2 ≤ (4 * x)^2 := by nlinarith [sq_nonneg x]
      calc
        (1 / (4 * x))^2 = 1 / (4 * x)^2 := by ring
        _ ≤ 1 / (1 + x^2) := one_div_le_one_div_of_le hdenPos hden

/-- NODE HE.CompactSupportConstruction.glued_weighted_square_left_bound
deps: HE.CompactSupportConstruction.glued_profile_left_exterior, HE.CompactSupportConstruction.critical_weight_cancels_exterior_gaussian, HE.CompactSupportConstruction.distinguished_exterior_profile_positive, HE.CompactSupportConstruction.distinguished_exterior_profile_mills_bound
statement: on the left tail, the critical weighted square is dominated by the standard integrable rational tail.
-/
lemma gluedWeightedSquare_left_bound {x : ℝ} (hx : x < -2) :
    gluedWeightedSquare x ≤ 1 / (1 + x^2) := by
  have hweighted : Real.exp (x^2) * gluedProfile x =
      exteriorProfile gaussianHalfMass (-x) := by
    rw [gluedProfile_eq_left (le_of_lt hx)]
    have h := weightedExteriorMaster_eq gaussianHalfMass (-x)
    convert h using 1 <;> ring
  rw [gluedWeightedSquare, hweighted]
  have hpos := exteriorProfile_halfMass_pos (by linarith : 0 ≤ -x)
  have hle := exteriorProfile_halfMass_le (by linarith : 0 < -x)
  have hrecip : 0 ≤ 1 / (4 * (-x)) := by
    exact one_div_nonneg.mpr (mul_nonneg (by norm_num) (by linarith))
  have hsquare : (exteriorProfile gaussianHalfMass (-x))^2 ≤
      (1 / (4 * (-x)))^2 := by
    nlinarith
  calc
    (exteriorProfile gaussianHalfMass (-x))^2 ≤ (1 / (4 * (-x)))^2 := hsquare
    _ ≤ 1 / (1 + x^2) := by
      have hdenPos : 0 < 1 + x^2 := by positivity
      have hden : 1 + x^2 ≤ (4 * (-x))^2 := by nlinarith [sq_nonneg x]
      calc
        (1 / (4 * (-x)))^2 = 1 / (4 * (-x))^2 := by ring
        _ ≤ 1 / (1 + x^2) := one_div_le_one_div_of_le hdenPos hden

/-- NODE HE.CompactSupportConstruction.glued_weighted_square_right_integrable
deps: HE.CompactSupportConstruction.glued_weighted_square_right_bound
statement: the critical weighted square is integrable on the right tail.
-/
lemma gluedWeightedSquare_integrableOn_right :
    MeasureTheory.IntegrableOn gluedWeightedSquare (Set.Ioi (2 : ℝ)) := by
  have hmajor : MeasureTheory.IntegrableOn
      (fun x : ℝ => 1 / (1 + x^2)) (Set.Ioi (2 : ℝ)) :=
    by simpa only [one_div] using integrable_inv_one_add_sq.integrableOn
  apply hmajor.mono' gluedWeightedSquare_continuous.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact gluedWeightedSquare_right_bound hx

/-- NODE HE.CompactSupportConstruction.glued_weighted_square_left_integrable
deps: HE.CompactSupportConstruction.glued_weighted_square_left_bound
statement: the critical weighted square is integrable on the left tail.
-/
lemma gluedWeightedSquare_integrableOn_left :
    MeasureTheory.IntegrableOn gluedWeightedSquare (Set.Iio (-2 : ℝ)) := by
  have hmajor : MeasureTheory.IntegrableOn
      (fun x : ℝ => 1 / (1 + x^2)) (Set.Iio (-2 : ℝ)) :=
    by simpa only [one_div] using integrable_inv_one_add_sq.integrableOn
  apply hmajor.mono' gluedWeightedSquare_continuous.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact gluedWeightedSquare_left_bound hx

/-- NODE HE.CompactSupportConstruction.glued_weighted_square_integrable
deps: HE.CompactSupportConstruction.glued_weighted_square_right_integrable, HE.CompactSupportConstruction.glued_weighted_square_left_integrable
statement: the critical weighted square of the global glued profile is integrable on the real line.
-/
lemma gluedWeightedSquare_integrable :
    MeasureTheory.Integrable gluedWeightedSquare := by
  have hmid : MeasureTheory.IntegrableOn gluedWeightedSquare
      (Set.Icc (-2 : ℝ) 2) :=
    gluedWeightedSquare_continuous.continuousOn.integrableOn_Icc
  have hall := (gluedWeightedSquare_integrableOn_left.union hmid).union
    gluedWeightedSquare_integrableOn_right
  have hcover :
      (Set.Iio (-2 : ℝ) ∪ Set.Icc (-2 : ℝ) 2) ∪ Set.Ioi (2 : ℝ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ,
      iff_true]
    by_cases hleft : x < -2
    · exact Or.inl (Or.inl hleft)
    · by_cases hright : 2 < x
      · exact Or.inr hright
      · exact Or.inl (Or.inr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
  rw [hcover, MeasureTheory.integrableOn_univ] at hall
  exact hall


end CompactSupportConstruction
end HardyCompactSupport

