# Strict Correctness Verification for the Lean Proof

[Chinese](strict-proof_CN.md)

A plain `lake build` only shows that Lean accepts the project. By itself, it does not exclude `sorry` from the source and does not confirm that conditions have not been silently removed from the main theorem. The stricter audit below addresses both concerns. Run every command from the project root.

## Step 1: Inspect All Local Changes

```powershell
git status --short
git diff -- HardyCompactSupport.lean HardyCompactSupport lakefile.lean lean-toolchain lake-manifest.json
```

This prevents unreviewed modifications from entering the audited state. If the auditor has a trusted commit, replace `<trusted-commit>` with its commit hash and compare the entry point and configuration directly:

```powershell
git diff <trusted-commit> -- HardyCompactSupport.lean lakefile.lean lean-toolchain lake-manifest.json
```

## Step 2: Search for Unfinished Proofs and Unsafe Bypasses

```powershell
$pattern = '\b(sorry|admit|axiom|unsafe|partial|native_decide|sorryAx|mkSorry|implemented_by|extern)\b|Lean\.ofReduceBool|debug\.skipKernelTC|set_option\s+warningAsError\s+false'
$hits = & rg -n --glob '*.lean' --glob '!.lake/**' $pattern . 2>&1
if ($LASTEXITCODE -eq 0) {
  $hits
  throw 'FAIL: found an unfinished proof, custom axiom, or unsafe bypass'
}
if ($LASTEXITCODE -gt 1) { throw "FAIL: rg failed: $hits" }
'PASS: no sorry, admit, custom axiom, or unsafe bypass found'
```

The expected output consists only of the final `PASS` line. This check does not ban `Classical.choice`, which is part of the classical foundation commonly used by Mathlib. The transitive axiom audit in Step 5 reports explicitly whether the main theorem depends on it.

Search separately for textual markers of unfinished work. This is a manual-review aid, not by itself evidence of a gap in a Lean proof:

```powershell
rg -n --glob '*.lean' --glob '!.lake/**' 'TODO|FIXME|UNFINISHED' .
```

No output means that none of these markers is present.

## Step 3: Verify the Toolchain and Dependency Repositories

```powershell
Get-Content lean-toolchain
lake env lean --version

$manifest = Get-Content lake-manifest.json -Raw | ConvertFrom-Json
foreach ($package in $manifest.packages | Where-Object type -eq 'git') {
  $directory = Join-Path $manifest.packagesDir $package.name
  $actual = git -C $directory rev-parse HEAD
  $dirty = git -C $directory status --porcelain
  "{0}: expected={1} actual={2}" -f $package.name, $package.rev, $actual
  if ($LASTEXITCODE -ne 0 -or $actual -ne $package.rev -or $dirty) {
    if ($dirty) { $dirty }
    throw "FAIL: dependency $($package.name) was replaced or modified"
  }
}
'PASS: all Git dependencies match lake-manifest.json and have clean worktrees'
```

This project is expected to use Lean `v4.31.0`. The expected Mathlib commit is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The auditor must also compare `lake-manifest.json` itself against a trusted commit; otherwise an attacker could modify both the manifest and the dependency directories.

## Step 4: Remove Only the Project Cache and Perform a Full Build

```powershell
$projectRoot = (Resolve-Path '.').Path
$projectBuild = [System.IO.Path]::GetFullPath((Join-Path $projectRoot '.lake/build'))
if ([System.IO.Path]::GetDirectoryName($projectBuild) -ne (Join-Path $projectRoot '.lake')) {
  throw "FAIL: refusing to delete a path outside the project: $projectBuild"
}
if ([System.IO.Directory]::Exists($projectBuild)) {
  [System.IO.Directory]::Delete($projectBuild, $true)
}

lake build
if ($LASTEXITCODE -ne 0) { throw 'FAIL: lake build failed' }
'PASS: full build succeeded without the old project .olean cache'
```

Do not use an untargeted `lake clean` here: it also deletes Mathlib's entire local build cache and needlessly recompiles thousands of dependency modules. Step 3 verifies the dependency source and commits separately. A successful `lake build` only proves that Lean accepts the source, so it must be evaluated together with Steps 2 and 5.

## Step 5: Pin the Exact Main Theorem Type and Inspect Transitive Axioms

The command below rewrites the full expected theorem type into the system temporary directory. If the public entry point removes any condition, changes a quantifier, or substitutes a weaker conclusion, the `example` will fail to type-check. The final `#print axioms` command reports every axiom used by the entire proof chain.

```powershell
$audit = Join-Path $env:TEMP 'HardyMainTheoremAudit.lean'
@'
import HardyCompactSupport

noncomputable section
open scoped ContDiff

example :
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
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsCompact (tsupport (V t))) ∧
      MeasureTheory.Integrable
        (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 0 x‖^2) ∧
      MeasureTheory.Integrable
        (fun x : ℝ => ‖((Real.exp (x^2 / 4) : ℝ) : ℂ) * u 1 x‖^2) :=
  HardyCompactSupport.exists_nontrivial_endpoint_solution_with_compactly_supported_real_potential

#print axioms HardyCompactSupport.exists_nontrivial_endpoint_solution_with_compactly_supported_real_potential
'@ | Set-Content -Encoding utf8 $audit

$axiomOutput = lake env lean $audit 2>&1 | Out-String
$leanExit = $LASTEXITCODE
[System.IO.File]::Delete($audit)
$axiomOutput
if ($leanExit -ne 0) { throw 'FAIL: the main theorem type changed, or the audit file did not compile' }

$match = [regex]::Match($axiomOutput, 'depends on axioms:\s*\[(?<list>[\s\S]*?)\]')
if (-not $match.Success) { throw 'FAIL: unable to parse the #print axioms output' }
$allowed = @('propext', 'Classical.choice', 'Quot.sound')
$actual = $match.Groups['list'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ }
$unexpected = $actual | Where-Object { $_ -notin $allowed }
if ($unexpected) { throw "FAIL: disallowed axioms found: $($unexpected -join ', ')" }
'PASS: the exact main theorem is unchanged and has no disallowed transitive axioms'
```

The expected axiom output is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are proposition extensionality, classical choice, and quotient soundness, respectively. They are standard foundational axioms used by Lean and Mathlib. The output must not contain `sorryAx`, any project-defined axiom, or `Lean.ofReduceBool`.

The trust boundary consists of the Lean kernel, the pinned toolchain, and the audit commands themselves. If this document's commands have been modified, recover them from a trusted Git commit before running them. No in-repository self-check can independently detect an attacker who can simultaneously alter the proof, the verification commands, and the trusted baseline.
