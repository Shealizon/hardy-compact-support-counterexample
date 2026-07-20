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

## 数学说明

### 1. 方程与临界端点条件

考虑一维含势 Schrodinger 方程

$$
i\partial_t u(t,x)+\partial_x^2u(t,x)=V(t,x)u(t,x),
\qquad (t,x)\in[0,1]\times\mathbb R.
$$

目标是构造一个非零光滑解 $u$ 和一个光滑、有界、实值的势 $V$，使得

$$
e^{x^2/4}u(0,x),\qquad e^{x^2/4}u(1,x)
$$

都属于 $L^2(\mathbb R)$。等价地，需要证明

$$
\int_{\mathbb R}e^{x^2/2}|u(0,x)|^2\,dx<\infty,
\qquad
\int_{\mathbb R}e^{x^2/2}|u(1,x)|^2\,dx<\infty.
$$

这里的系数 $1/4$ 正是归一化时间区间 $[0,1]$ 上使用的 Hardy 临界 Gaussian 权重。

### 2. 时间宽度与相似变量

定义

$$
q(t)=(1-t)^2+t^2,
\qquad
y(t)=2\sqrt{q(t)},
\qquad
s=\frac{x}{y(t)}.
$$

因为

$$
q(t)=2\left(t-\frac12\right)^2+\frac12>0,
$$

所以 $y(t)$ 在所有时刻都严格为正。它还满足

$$
y(t)^2=4q(t),
\qquad
y''(t)=\frac{16}{y(t)^3}.
$$

相似变量 $s=x/y(t)$ 把随时间变化的空间尺度转换为一个固定剖面变量。

### 3. Gaussian 尾部外解

从 Gaussian 核

$$
K(x)=e^{-2x^2}
$$

出发，令

$$
J(x)=\int_0^x e^{-2s^2}\,ds,
\qquad
C_{\ast}=\int_0^\infty e^{-2s^2}\,ds.
$$

定义外部函数

$$
H_C(x)=e^{2x^2}\bigl(C-J(x)\bigr),
\qquad
F_C(x)=e^{-x^2}H_C(x).
$$

选择 $C=C_{\ast}$ 后，在 $x\ge 0$ 上有

$$
C_{\ast}-J(x)=\int_x^\infty e^{-2s^2}\,ds>0.
$$

因此 $F_{C_{\ast}}$ 是正的衰减外解，并满足

$$
F_{C_{\ast}}''(x)=\bigl(4x^2+2\bigr)F_{C_{\ast}}(x).
$$

Gaussian 尾积分估计还给出临界加权可积性。证明在负半轴使用反射函数 $F_{C_{\ast}}(-x)$。

### 4. 正剖面的平滑拼接

取两个光滑过渡函数 $\chi_+$ 和 $\chi_-$，把右侧外解、中心常数函数 $1$ 和左侧反射外解拼成

$$
P(x)=1+\chi_+(x)\bigl(F_{C_{\ast}}(x)-1\bigr)
       +\chi_-(x)\bigl(F_{C_{\ast}}(-x)-1\bigr).
$$

构造保证

$$
P\in C^\infty(\mathbb R),
\qquad
P(x)>0,
\qquad
P(0)=1.
$$

因为 $P$ 从不为零，可以定义剖面余项

$$
r(x)=\frac{P''(x)}{P(x)}-4x^2.
$$

于是恒有振子型方程

$$
P''(x)=\bigl(4x^2+r(x)\bigr)P(x).
$$

在拼接区间之外，$P$ 就是外解或其反射，因此

$$
r(x)=2
$$

在充分大的 $|x|$ 上成立。同时，构造证明了

$$
\int_{\mathbb R}\bigl(e^{x^2}P(x)\bigr)^2\,dx<\infty.
$$

### 5. 解与实势的构造

令

$$
b(t)=\frac{2t-1}{4q(t)},
\qquad
r_{\mathrm{ext}}=2,
$$

这里 $r_{\mathrm{ext}}$ 表示剖面余项 $r$ 在拼接区域外的常值；Lean 定义中的字段名是 `remainderInf`。它不是另一个函数，也不是 `arc_infty`。

定义振幅和相位

$$
A(t,x)=\frac{1}{\sqrt{y(t)}}P\left(\frac{x}{y(t)}\right),
$$

$$
\phi(t,x)=b(t)x^2+\frac{r_{\mathrm{ext}}}{4}\arctan(2t-1).
$$

候选解为

$$
u(t,x)=A(t,x)e^{i\phi(t,x)},
$$

势函数为

$$
V(t,x)=
\frac{r\left(x/y(t)\right)-r_{\mathrm{ext}}}{y(t)^2}.
$$

这个公式直接说明 $V$ 是实值函数。

由于 $r-r_{\mathrm{ext}}$ 有界且 $y(t)$ 始终远离零，势函数 $V(t,x)$ 在 $[0,1]\times\mathbb R$ 上一致有界。

### 6. Schrodinger 恒等式

把 $u=Ae^{i\phi}$ 代入方程后，剩余项分成实部和虚部。虚部由振幅输运恒等式消去，实部则由

$$
P''(s)=\bigl(4s^2+r(s)\bigr)P(s),
\qquad
y''(t)=\frac{16}{y(t)^3}
$$

以及相位导数恒等式消去。最终得到逐点等式

$$
i\partial_tu+\partial_x^2u=Vu.
$$

此外，当 $|x/y(t)|$ 充分大时 $r(x/y(t))=r_{\mathrm{ext}}$，所以对应的 $V(t,x)$ 等于零。

### 7. 两个端点的 Gaussian 衰减

在 $t=0$ 和 $t=1$ 时，

$$
y(0)=y(1)=2,
\qquad
s=\frac{x}{2}.
$$

相位因子的模恒为 $1$，因此两个端点都有

$$
\left|e^{x^2/4}u(t,x)\right|^2
=\frac12\left(e^{(x/2)^2}P(x/2)\right)^2,
\qquad t\in\{0,1\}.
$$

右侧的可积性正是剖面加权可积性经过变量缩放后的结果，由此得到两个临界端点条件。

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

### 严格正确性审计

完整步骤见 [strict-proof.md](strict-proof.md)。

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
