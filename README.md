# Hardy 端点紧支撑实势反例的 Lean 形式化

本项目使用 Lean 4 和 Mathlib，形式化一维 Schrodinger 方程在 Hardy 不确定性原理临界端点处的一个非平凡解：存在光滑、有界、实值的势函数，并且势函数在每个固定时刻都具有紧支撑，而解在两个端点时刻满足临界 Gaussian 加权可积性。

## 主定理

主定理位于 [`HardyCompactSupport.lean`](HardyCompactSupport.lean)：

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

它逐项表达以下结论：

1. `u` 是复值光滑函数，`V` 是实值光滑函数。
2. 存在某个 `t ∈ [0,1]` 和 `x ∈ ℝ`，使得 `u t x ≠ 0`。
3. `u` 和 `V` 逐点满足一维 Schrodinger 方程。
4. `V` 在整个时间区间上一致有界。
5. 对每个固定时刻 `t`，`V t` 的拓扑支撑 `tsupport (V t)` 是 `ℝ` 中的紧集。
6. `u 0` 和 `u 1` 满足临界 Gaussian 加权平方可积性。

### 关于紧支撑条件

主定理没有引入统一半径 `R`，而是直接使用紧支撑的内在定义：

```lean
∀ t ∈ Set.Icc (0 : ℝ) 1, IsCompact (tsupport (V t))
```

证明内部会先得到势函数在某个依赖于时间的闭区间之外为零，再证明其函数支撑的闭包包含于该闭区间。这个中间半径只服务于证明，不属于主定理的结论。

## 证明结构

证明按照依赖关系拆分为以下模块：

| 模块 | 作用 |
| --- | --- |
| `AlgebraicIdentities.lean` | 基础有理式与次数恒等式 |
| `WidthEquation.lean` | 宽度函数满足的常微分方程 |
| `TimeScaling.lean` | 时间缩放、宽度正性和导数公式 |
| `PhaseEquation.lean` | 相位与输运系数恒等式 |
| `ConstructionStatement.lean` | 中间构造所需的结构化命题 |
| `ResidualIdentity.lean` | Schrodinger 剩余项的代数消去 |
| `DecayEstimates.lean` | 非零性、有界性和端点衰减的中间结论 |
| `ExplicitSolution.lean` | 显式解、相位和势函数的导数计算 |
| `GaussianTailProfile.lean` | Gaussian 尾积分与外部剖面 |
| `PositiveProfile.lean` | 正光滑剖面的拼接与加权可积性 |
| `ConstructedSolution.lean` | 最终解和势函数的定义及光滑性 |
| `SchrodingerIdentity.lean` | 构造函数满足 Schrodinger 方程 |
| `EndpointDecayAndSupport.lean` | 有界性、区间外消失和端点积分 |
| `EndpointVerification.lean` | 将区间外消失转化为拓扑支撑紧性 |

公开入口只导入最后一个验证模块，因此读者可以先阅读主定理，再沿导入链逐层查看细节。

## 构建与检查

项目使用 Lean `v4.31.0` 和对应版本的 Mathlib。

```powershell
lake update
lake build
```

只检查主定理入口：

```powershell
lake env lean HardyCompactSupport.lean
```

重新生成证明状态报告：

```powershell
python scripts/generate_status.py
```

当前状态见 [`STATUS.md`](STATUS.md)：全部 208 个定理和引理均已完成，源码中没有证明占位符，也没有导入归档的旧证明模块。

## 目录

```text
.
├── HardyCompactSupport.lean       # 完整展开条件的主定理入口
├── HardyCompactSupport/           # 分层证明模块
├── scripts/generate_status.py     # 构建与证明数量检查
├── STATUS.md                      # 人类可读状态报告
├── status.json                    # 机器可读状态报告
├── lakefile.lean
└── lean-toolchain
```
