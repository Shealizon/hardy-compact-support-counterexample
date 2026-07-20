# Lean 证明严格正确性检验

普通的 `lake build` 只能说明 Lean 接受了项目；它不能单独排除文件中存在
`sorry`，也不能确认主定理的条件没有被悄悄删改。因此这里采用了更加严格的检验。所有命令都在项目根目录执行。

## 第一步：查看所有本地改动

```powershell
git status --short
git diff -- HardyCompactSupport.lean HardyCompactSupport lakefile.lean lean-toolchain lake-manifest.json
```

这一步能防止把未经查看的修改混入验收。若审计者保存了一个
可信提交，还应将 `<可信提交>` 换成它的提交号，直接比较入口和配置：

```powershell
git diff <可信提交> -- HardyCompactSupport.lean lakefile.lean lean-toolchain lake-manifest.json
```

## 第二步：搜索未完成证明和危险绕过

```powershell
$pattern = '\b(sorry|admit|axiom|unsafe|partial|native_decide|sorryAx|mkSorry|implemented_by|extern)\b|Lean\.ofReduceBool|debug\.skipKernelTC|set_option\s+warningAsError\s+false'
$hits = & rg -n --glob '*.lean' --glob '!.lake/**' $pattern . 2>&1
if ($LASTEXITCODE -eq 0) {
  $hits
  throw 'FAIL: 发现未完成证明、公理或危险绕过'
}
if ($LASTEXITCODE -gt 1) { throw "FAIL: rg 执行错误：$hits" }
'PASS: 未发现 sorry、admit、自定义 axiom 或危险绕过'
```

预期输出只有最后一行 `PASS`。这里不禁止 `Classical.choice`：它是 Mathlib 通常采用的
经典逻辑基础之一，稍后的传递公理检查会明确显示它是否被主定理使用。

另行查看尚未完成的文字标记；这一项用于人工复核，不等同于 Lean 证明漏洞：

```powershell
rg -n --glob '*.lean' --glob '!.lake/**' 'TODO|FIXME|UNFINISHED' .
```

无输出表示没有这些标记。

## 第三步：核对工具链和依赖仓库

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
    throw "FAIL: 依赖 $($package.name) 被替换或修改"
  }
}
'PASS: 所有 Git 依赖均与 lake-manifest.json 一致且工作区干净'
```

本项目预期使用 Lean `v4.31.0`；Mathlib 提交应为
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。同时必须从可信提交核对
`lake-manifest.json` 本身，否则攻击者可以同时修改清单和依赖目录。

## 第四步：只清除本项目缓存并完整构建

```powershell
$projectRoot = (Resolve-Path '.').Path
$projectBuild = [System.IO.Path]::GetFullPath((Join-Path $projectRoot '.lake/build'))
if ([System.IO.Path]::GetDirectoryName($projectBuild) -ne (Join-Path $projectRoot '.lake')) {
  throw "FAIL: 拒绝删除项目外路径：$projectBuild"
}
if ([System.IO.Directory]::Exists($projectBuild)) {
  [System.IO.Directory]::Delete($projectBuild, $true)
}

lake build
if ($LASTEXITCODE -ne 0) { throw 'FAIL: lake build 失败' }
'PASS: 无旧项目 .olean 缓存的完整构建成功'
```

不要在这里使用不带目标的 `lake clean`：它还会删除 Mathlib 的全部本地构建缓存，
导致数千个依赖模块被无谓地重新编译。依赖源码和提交已在第三步单独核验。
`lake build` 成功只证明源码被 Lean 接受，必须与第二步和第五步一起判断。

## 第五步：锁定主定理原文并检查传递公理

下面的命令在系统临时目录中重新写出完整的预期定理类型。若原入口删掉任何条件、
改变量词或换成较弱结论，`example` 将无法通过类型检查。最后的 `#print axioms`
检查整个证明链实际依赖了哪些公理。

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
if ($leanExit -ne 0) { throw 'FAIL: 主定理类型已改变，或审计文件无法编译' }

$match = [regex]::Match($axiomOutput, 'depends on axioms:\s*\[(?<list>[\s\S]*?)\]')
if (-not $match.Success) { throw 'FAIL: 无法读取 #print axioms 输出' }
$allowed = @('propext', 'Classical.choice', 'Quot.sound')
$actual = $match.Groups['list'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ }
$unexpected = $actual | Where-Object { $_ -notin $allowed }
if ($unexpected) { throw "FAIL: 出现未许可公理：$($unexpected -join ', ')" }
'PASS: 主定理原文未改变，且没有未许可的传递公理'
```

当前正常的公理输出应当只有：

```text
[propext, Classical.choice, Quot.sound]
```

它们分别对应命题外延性、经典选择和商类型相等性，是 Lean/Mathlib 常见的基础公理；
输出中绝不能出现 `sorryAx`、项目自行声明的公理或 `Lean.ofReduceBool`。

这里的信任边界是 Lean 内核、固定版本的工具链与审计命令本身。如果本文中的
审计命令也被修改，必须从可信 Git 提交取回审计命令再运行。攻击者若能
同时修改证明、检查命令和可信基线，任何仓库内自检都无法独立识别这种情况。
