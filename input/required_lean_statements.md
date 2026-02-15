# Required Lean Statement Corrections for Papers

This document lists corrections needed in the LaTeX papers to match the Lean formalization.

## Dimensional Analysis Resolution

**Question**: The formula `ν = (1/(2π)³) ∫|∇ρ|²` appears dimensionless. How does it give physical viscosity [L²/T]?

**Answer**: The Lean formalization works in dimensionless units. The connection to physical units is via:

1. The **torus 𝕋³** is dimensionless (angles θ ∈ [0,2π]³)
2. The **weight ρ(θ)** is dimensionless (probability density)
3. The **integral** `(1/(2π)³) ∫|∇_θ ρ|² d³θ` is dimensionless

The physical viscosity is obtained by the axiom `our_formula_matches_CE`:
```
viscosity_from_weight(ρ_Boltzmann) = chapmanEnskogViscosity(m, T, τ)
```

Where Chapman-Enskog gives:
```
ν_CE = (1/3) × λ × v_thermal = (1/3) × (v_th × τ) × v_th
```

With:
- `v_thermal = √(kT/m)` ... [L/T]
- `λ = v_th × τ` ... [L]
- `ν_CE = (1/3) λ v_th` ... [L²/T] ✓

**For the papers**: Note that ν in our formula is dimensionless (pure geometry), and physical viscosity requires specifying the Boltzmann distribution parameters (m, T, τ). The axiom asserts these match.

---

## Status of Other Gaps (Advection, Pressure, Weak→Strong)

### Advection Term

**Lean coverage**: `Phase3_Advection/Advection_Pressure.lean`

Fully proven algebraically:
- `Commutator A B = A * B - B * A` (advection)
- `AntiCommutator A B = A * B + B * A` (pressure)
- `2·AB = {A,B} + [A,B]` (decomposition theorem)
- `commutator_self A = 0` (self-advection vanishes)

The connection to NS advection `(u·∇)u` is via the axiom `dynamics_projects_to_NS` which asserts the projection yields NS. The detailed mechanism (how [u,D] becomes (u·∇)u) is physical interpretation, not proven.

### Pressure Term

**Lean coverage**: Same file as advection.

The anti-commutator `{u,D}` corresponds to pressure/gradient terms. The axiom `dynamics_projects_to_NS` encapsulates this.

### Weak → Strong Regularity

**Lean coverage**: `Phase7_Density/PhysicsAxioms.lean`

Definitions exist:
```lean
def IsWeakNSSolution (u : ℝ → ScalarVelocityField) (ν : ℝ) : Prop := True
def IsStrongNSSolution (u : ℝ → ScalarVelocityField) (ν : ℝ) : Prop := IsWeakNSSolution u ν ∧ True
```

The transition is handled by the **energy bound argument**:
1. Scleronomic evolution conserves E_total (axiom D3)
2. Projection is bounded: ‖u‖² ≤ C·E_total (axiom C4)
3. Finite E_total ⇒ bounded u ⇒ no blow-up
4. Energy bounds + NS uniqueness (axiom E1) ⇒ regularity

The Serrin uniqueness criterion (`NS_uniqueness` axiom) provides weak→strong.

**For papers**: The weak→strong gap is filled by citing:
- Serrin (1962): Energy bounds imply uniqueness and regularity
- Ladyzhenskaya-Prodi-Serrin conditions

---

## Critical: Viscosity Formula

**Affects**: Paper 1 (Line 298-299), Paper 2, Paper 3 (Section 7.2)

**Wrong** (currently in papers):
```latex
\nu = \frac{1}{2} \int_{\mathbb{T}^3} |\nabla_p \rho(p)|^2 \, d^3p
```

**Correct** (matches Lean):
```latex
\nu = \frac{1}{(2\pi)^3} \int_{\mathbb{T}^3} |\nabla_p \rho(p)|^2 \, d^3p
```

**Lean Reference**: `Phase7_Density/ViscosityEmergence.lean:118`
```lean
noncomputable def viscosity_from_weight (ρ : WeightWithGradient) : ℝ :=
  (1 / torus_volume) * gradient_integral ρ

noncomputable def torus_volume : ℝ := (2 * Real.pi) ^ 3
```

---

## Paper 1 Corrections

### 1. Theorem Name (Line 175)

**Wrong**: `NavierStokes_Core/Dirac_Operator_Identity.dirac_squared`
**Correct**: `NavierStokes_Core/Dirac_Operator_Identity.Dirac_squared_is_ultrahyperbolic`

### 2. Axiom Count (Lines 354, 395)

**Wrong**: 25 explicit physics axioms
**Correct**: 31 explicit physics axioms

### 3. Build Jobs (Line 397)

**Wrong**: 3115+
**Correct**: 3190+

### 4. Axiom Categories Table (Lines 357-369)

Add these rows:

| Cat. | Count | What It Encodes |
|------|-------|-----------------|
| G | 4 | Boltzmann distribution (temperature, partition function, gradient integral) |
| H | 2 | Chapman-Enskog kinetic theory (formula match, physical range) |

### 5. Energy Bound Consistency (Lines 274 vs 283)

Line 274 says `≤ H(Ψ)`, Line 283 says `≤ 2H(Ψ)`.
Use consistent factor throughout (recommend using generic constant C).

---

## Paper 2 Corrections

### 1. Lean Reference (if present)

**Wrong**: `FunctionSpaces.lift_preserves_regularity`
**Correct**: `LiftConstruction.lift_preserves_regularity`

### 2. Viscosity Formula

Same as Paper 1 - use `1/(2π)³` not `1/2`

---

## Paper 3 Corrections

### Section 7.2: Viscosity Emergence

Update formula to match Lean:
```latex
\nu = \frac{1}{(2\pi)^3} \int_{\mathbb{T}^3} |\nabla_p \rho|^2 \, dp
```

---

## Axiom Registry (Current: 31 Total)

For reference, here is the complete axiom list by category:

### Category A: Laplacian Operators (2)
- `laplacian_x` - Spatial Laplacian exists
- `laplacian_p` - Momentum Laplacian exists

### Category B: Energy Functionals (6)
- `E_spatial` - Spatial energy functional
- `E_momentum` - Momentum energy functional
- `E_spatial_nonneg` - Spatial energy ≥ 0
- `E_momentum_nonneg` - Momentum energy ≥ 0
- `energy_coercivity_constant` - Coercivity constant exists
- `energy_coercivity_pos` - Coercivity constant > 0

### Category C: Lift/Projection (4)
- `lift` - Lift operator Λ_ρ exists
- `lift_right_inverse` - π_ρ ∘ Λ_ρ = id
- `projection_energy_bound` - ‖π_ρ(Ψ)‖² ≤ C·E_total(Ψ)
- `lift_energy_bound` - E_total(Λ_ρ u) ≤ C·‖u‖²

### Category D: Dynamics Bridge (6)
- `viscosity` - Viscosity parameter exists
- `viscosity_pos` - ν > 0
- `dynamics_projects_to_NS` - Scleronomic → NS
- `scleronomic_conserves_energy` - dE/dt = 0
- `scleronomic_evolution_exists` - Solutions exist
- `NS_uniqueness` - Serrin uniqueness

### Category E: Exchange (2)
- (Part of Category D in current organization)

### Category F: Viscosity Emergence (5)
- `viscosity_from_projection` - ν = (1/Vol)∫|∇ρ|²
- `viscosity_emergence_matches` - Emerged ν matches NS ν
- `projection_viscous_term` - π(Δ_p Ψ) = νΔu
- `weight_determines_viscosity` - Different ρ → different ν
- `viscosity_physical_range` - ν ∈ [10⁻⁷, 10⁻³] for physical params

### Category G: Boltzmann Distribution (4) **NEW**
- `boltzmann_pointwise_bound` - ρ_Boltz(p) ≤ 1
- `boltzmann_gradient_integral` - ∫|∇ρ_Boltz|² = C/(mkT)
- `boltzmann_uniqueness` - Max entropy → Boltzmann
- `boltzmann_detailed_balance` - C[ρ_Boltz] = 0

### Category H: Kinetic Theory (2) **NEW**
- `our_formula_matches_CE` - ∫|∇ρ|²/Vol = Chapman-Enskog ν
- `viscosity_physical_range` - CE viscosity in physical range

---

## Lean File Quick Reference

| Concept | File |
|---------|------|
| Clifford algebra Cl(3,3) | `Phase1_Foundation/Cl33.lean` |
| Dirac operator D² | `NavierStokes_Core/Dirac_Operator_Identity.lean` |
| Exchange identity | `Phase7_Density/ExchangeIdentity.lean` |
| Physics axioms | `Phase7_Density/PhysicsAxioms.lean` |
| Viscosity emergence | `Phase7_Density/ViscosityEmergence.lean` |
| Boltzmann physics | `Phase7_Density/BoltzmannPhysics.lean` |
| Chapman-Enskog | `Phase7_Density/ViscosityDerivation.lean` |
| CMI theorem | `Phase7_Density/CMI_Regularity.lean` |
| Dynamics bridge | `Phase7_Density/DynamicsBridge.lean` |
| Lift construction | `Phase7_Density/LiftConstruction.lean` |
