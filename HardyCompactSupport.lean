import HardyCompactSupport.EndpointVerification

/-!
# Hardy endpoint counterexample with a compactly supported real potential

The main theorem is stated here in full.  Every hypothesis and conclusion is
visible without unfolding an auxiliary proposition or certificate.
-/

noncomputable section

open scoped ContDiff

namespace HardyCompactSupport

open CompactSupportConstruction

/--
There are a nontrivial smooth solution `u` and a smooth bounded real scalar
potential `V` for the one-dimensional Schrodinger equation on `[0,1]`.
For every time in this interval, the topological support of `V(t, ·)` is a
compact subset of `ℝ`.  At times zero and one, `u` has the critical Gaussian
weighted `L²` decay.
-/
theorem exists_nontrivial_endpoint_solution_with_compactly_supported_real_potential :
    ∃ (u : ℝ → ℝ → ℂ) (V : ℝ → ℝ → ℝ) (potentialBound : ℝ),
      0 ≤ potentialBound ∧
      ContDiff ℝ ∞ (Function.uncurry u) ∧
      ContDiff ℝ ∞ (Function.uncurry V) ∧
      (∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ x : ℝ, u t x ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
        Complex.I * deriv (fun τ : ℝ => u τ x) t +
            deriv (deriv (fun ξ : ℝ => u t ξ)) x =
          (V t x : ℂ) * u t x) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
        |V t x| ≤ potentialBound) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        IsCompact (tsupport (V t))) ∧
      MeasureTheory.Integrable
        (fun x : ℝ =>
          ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 0 x‖^2) ∧
      MeasureTheory.Integrable
        (fun x : ℝ =>
          ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 1 x‖^2) := by
  refine ⟨compactSolution compactProfileData,
    compactPotential compactProfileData,
    compactProfileData.remainderBound,
    compactProfileData.remainderBound_nonneg,
    compactCandidate_smooth.1,
    compactCandidate_smooth.2,
    compactCandidate_nonzero,
    compactCandidate_schrodinger,
    compactCandidate_bounded,
    EndpointVerification.constructedPotential_has_compact_support,
    compactCandidate_endpoint_integrable.1,
    compactCandidate_endpoint_integrable.2⟩

end HardyCompactSupport
