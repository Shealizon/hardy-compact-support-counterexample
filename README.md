# Lean Formalization of a Hardy Endpoint Counterexample with a Compactly Supported Real Potential

[![Lean CI](https://github.com/Shealizon/hardy-compact-support-counterexample/actions/workflows/lean-ci.yml/badge.svg?branch=main)](https://github.com/Shealizon/hardy-compact-support-counterexample/actions/workflows/lean-ci.yml)

[Chinese](README_CN.md)

This project uses Lean 4 and Mathlib to formalize a nontrivial solution of the one-dimensional Schrodinger equation at the critical endpoint of the Hardy uncertainty principle. It proves the existence of a smooth, bounded, real-valued potential whose spatial support is compact at every fixed time, together with a solution satisfying critical Gaussian weighted integrability at both endpoint times.

## Main Theorem

The main theorem is stated in [`HardyCompactSupport.lean`](HardyCompactSupport.lean):

```lean
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
        (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 0 x‖^2) ∧
      MeasureTheory.Integrable
        (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 1 x‖^2)
```

It states the following properties explicitly:

1. `u` is a smooth complex-valued function and `V` is a smooth real-valued function.
2. There are `t ∈ [0,1]` and `x ∈ ℝ` such that `u t x ≠ 0`.
3. `u` and `V` satisfy the one-dimensional Schrodinger equation pointwise.
4. `V` is uniformly bounded throughout the time interval.
5. For each fixed time `t`, the topological support `tsupport (V t)` is a compact subset of `ℝ`.
6. `u 0` and `u 1` satisfy the critical Gaussian weighted square-integrability condition.

## Mathematical Overview

### 1. Equation and Critical Endpoint Condition

Consider the one-dimensional Schrodinger equation with a potential:

$$
i\partial_t u(t,x)+\partial_x^2u(t,x)=V(t,x)u(t,x),
\qquad (t,x)\in[0,1]\times\mathbb R.
$$

The goal is to construct a nonzero smooth solution $u$ and a smooth, bounded, real-valued potential $V$ such that

$$
e^{x^2/4}u(0,x),\qquad e^{x^2/4}u(1,x)
$$

both belong to $L^2(\mathbb R)$. Equivalently, one must prove

$$
\int_{\mathbb R}e^{x^2/2}|u(0,x)|^2\,dx<\infty,
\qquad
\int_{\mathbb R}e^{x^2/2}|u(1,x)|^2\,dx<\infty.
$$

The coefficient $1/4$ is the critical Hardy Gaussian weight for the normalized time interval $[0,1]$.

### 2. Time-Dependent Width and Similarity Variable

Define

$$
q(t)=(1-t)^2+t^2,\qquad
y(t)=2\sqrt{q(t)},\qquad
s=\frac{x}{y(t)}.
$$

Since

$$
q(t)=2\left(t-\frac12\right)^2+\frac12>0,
$$

$y(t)$ is strictly positive at every time. It also satisfies

$$
y(t)^2=4q(t),\qquad
y''(t)=\frac{16}{y(t)^3}.
$$

The similarity variable $s=x/y(t)$ converts the time-dependent spatial scale into a fixed profile variable.

### 3. Gaussian-Tail Exterior Solution

Start from the Gaussian kernel

$$
K(x)=e^{-2x^2}
$$

and define

$$
J(x)=\int_0^x e^{-2s^2}\,ds,\qquad
C_{\ast}=\int_0^\infty e^{-2s^2}\,ds.
$$

For a constant $C$, define the exterior functions

$$
H_C(x)=e^{2x^2}\bigl(C-J(x)\bigr),\qquad
F_C(x)=e^{-x^2}H_C(x).
$$

With $C=C_{\ast}$, for $x\ge 0$ one has

$$
C_{\ast}-J(x)=\int_x^\infty e^{-2s^2}\,ds>0.
$$

Consequently, $F_{C_{\ast}}$ is a positive decaying exterior solution satisfying

$$
F_{C_{\ast}}''(x)=\bigl(4x^2+2\bigr)F_{C_{\ast}}(x).
$$

Gaussian tail estimates also give the required critical weighted integrability. On the negative half-line, the construction uses the reflected function $F_{C_{\ast}}(-x)$.

### 4. Smooth Gluing of a Positive Profile

Choose two smooth cutoff functions $\chi_+$ and $\chi_-$. Glue the right exterior solution, the central constant function $1$, and the reflected left exterior solution into

$$
P(x)=1+\chi_+(x)\bigl(F_{C_{\ast}}(x)-1\bigr)
       +\chi_-(x)\bigl(F_{C_{\ast}}(-x)-1\bigr).
$$

The construction ensures

$$
P\in C^\infty(\mathbb R),\qquad
P(x)>0,\qquad
P(0)=1.
$$

Because $P$ never vanishes, define the profile remainder

$$
r(x)=\frac{P''(x)}{P(x)}-4x^2.
$$

The oscillator-type equation

$$
P''(x)=\bigl(4x^2+r(x)\bigr)P(x)
$$

then holds identically. Outside the gluing region, $P$ equals an exterior solution or its reflection, so $r(x)=2$ for all sufficiently large $|x|$. The construction also proves

$$
\int_{\mathbb R}\bigl(e^{x^2}P(x)\bigr)^2dx<\infty.
$$

### 5. Construction of the Solution and Real Potential

Let

$$
b(t)=\frac{2t-1}{4q(t)},\qquad
r_{\mathrm{ext}}=2,
$$

where $r_{\mathrm{ext}}$ is the constant value of the profile remainder $r$ outside the gluing region. The corresponding field in the Lean definition is named `remainderInf`.

Define the amplitude and phase by

$$
A(t,x)=\frac{1}{\sqrt{y(t)}}P\left(\frac{x}{y(t)}\right),
$$

$$
\phi(t,x)=b(t)x^2+\frac{r_{\mathrm{ext}}}{4}\arctan(2t-1).
$$

The candidate solution and potential are

$$
u(t,x)=A(t,x)e^{i\phi(t,x)},
$$

$$
V(t,x)=\frac{r\left(x/y(t)\right)-r_{\mathrm{ext}}}{y(t)^2}.
$$

This formula directly shows that $V$ is real-valued. Since $r-r_{\mathrm{ext}}$ is bounded and $y(t)$ stays uniformly away from zero, $V(t,x)$ is uniformly bounded on $[0,1]\times\mathbb R$.

### 6. Schrodinger Identity

Substituting $u=Ae^{i\phi}$ into the equation separates the residual into real and imaginary parts. The amplitude transport identity cancels the imaginary part. The real part is canceled using

$$
P''(s)=\bigl(4s^2+r(s)\bigr)P(s),\qquad
y''(t)=\frac{16}{y(t)^3},
$$

together with the phase derivative identities. This yields the pointwise equality

$$
i\partial_tu+\partial_x^2u=Vu.
$$

Moreover, when $|x/y(t)|$ is sufficiently large, $r(x/y(t))=r_{\mathrm{ext}}$, and hence $V(t,x)=0$.

### 7. Gaussian Decay at the Two Endpoints

At $t=0$ and $t=1$,

$$
y(0)=y(1)=2,\qquad
s=\frac{x}{2}.
$$

The phase factor has modulus $1$, so at both endpoints

$$
\left|e^{x^2/4}u(t,x)\right|^2
=\frac12\left(e^{(x/2)^2}P(x/2)\right)^2,
\qquad t\in\{0,1\}.
$$

The right-hand side is integrable by the weighted profile estimate after a change of variables. This proves both critical endpoint conditions.

## Proof Structure

The proof is divided into the following modules according to their dependencies:

| Module | Role |
| --- | --- |
| `AlgebraicIdentities.lean` | Basic rational and polynomial-degree identities |
| `WidthEquation.lean` | Ordinary differential equation satisfied by the width function |
| `TimeScaling.lean` | Time scaling, positivity of the width, and derivative formulas |
| `PhaseEquation.lean` | Phase and transport-coefficient identities |
| `ConstructionStatement.lean` | Structured propositions required by the intermediate construction |
| `ResidualIdentity.lean` | Algebraic cancellation of the Schrodinger residual |
| `DecayEstimates.lean` | Intermediate nontriviality, boundedness, and endpoint decay results |
| `ExplicitSolution.lean` | Derivative calculations for the explicit solution, phase, and potential |
| `GaussianTailProfile.lean` | Gaussian tail integrals and the exterior profile |
| `PositiveProfile.lean` | Gluing of a smooth positive profile and weighted integrability |
| `ConstructedSolution.lean` | Definitions and smoothness of the final solution and potential |
| `SchrodingerIdentity.lean` | Verification of the Schrodinger equation |
| `EndpointDecayAndSupport.lean` | Boundedness, exterior vanishing, and endpoint integrals |
| `EndpointVerification.lean` | Conversion of exterior vanishing into compact topological support |

The public entry point imports only the final verification module. A reader can therefore start with the main theorem and follow the import chain into progressively finer details.

## Build and Verification

The project uses Lean `v4.31.0` and the corresponding Mathlib release.

```powershell
lake update
lake build
```

To check only the main theorem entry point:

```powershell
lake env lean HardyCompactSupport.lean
```

To regenerate the proof-status report:

```powershell
python scripts/generate_status.py
```

See [`STATUS.md`](STATUS.md) for the current status. All 208 theorems and lemmas are complete, the source contains no proof placeholders, and the archived legacy proof modules are not imported.

### Strict Correctness Audit

See [strict-proof.md](strict-proof.md) for the complete procedure.

## Directory Layout

```text
.
├── HardyCompactSupport.lean       # Main theorem entry point with all conditions expanded
├── HardyCompactSupport/           # Layered proof modules
├── scripts/generate_status.py     # Build and theorem-count checks
├── README_CN.md                   # Chinese version of this document
├── strict-proof.md                # Strict proof-audit procedure
├── strict-proof_CN.md             # Chinese version of the audit procedure
├── STATUS.md                      # Human-readable status report
├── status.json                    # Machine-readable status report
├── lakefile.lean
└── lean-toolchain
```
