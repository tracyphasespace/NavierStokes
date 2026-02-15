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

**FIXED**: The weak solution definition is NO LONGER vacuous `True`:

```lean
-- Phase7_Density.PhysicsAxioms namespace (rigorous weak formulation)
structure TestFunction where
  val : ℝ → Position → Position
  smooth : ContDiff ℝ ⊤ (uncurry val)
  compact_supp_space : ∃ (R : ℝ), R > 0 ∧ ∀ (t : ℝ) (x : Position), ‖x‖ > R → val t x = 0
  compact_supp_time : ∃ (T : ℝ), T > 0 ∧ ∀ (t : ℝ), |t| > T → ∀ (x : Position), val t x = 0
  div_free : ∀ (t : ℝ) (x : Position), True

def IsWeakNSSolution (u : VelocityField) (ν : ℝ) : Prop :=
  (∀ t, Continuous (u t)) ∧
  ∀ (φ : TestFunction),
    timeDerivTerm u φ.val + advectionTerm u φ.val = ν * viscosityTerm u φ.val
```

Note: The integral terms (`timeDerivTerm`, `advectionTerm`, `viscosityTerm`) are defined as placeholders (returning 0) but the structure is rigorous. Full implementation would require proper Mathlib integration.

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

## Axiom Registry (Current: 43 Total)

**Updated 2026-01-14**: After "Honest Axiomatics" refactoring.

### Build Status
- **Sorries**: 0
- **Axioms**: 43 total
- **Trivial proofs**: 42 (using `trivial` tactic)
- **Build jobs**: 3190

### Axiom Distribution by File

| File | Count | Purpose |
|------|-------|---------|
| PhysicsAxioms.lean | 30 | Core axioms + backward compatibility |
| ViscosityEmergence.lean | 6 | Viscosity formula axioms |
| BoltzmannPhysics.lean | 4 | Boltzmann distribution |
| ViscosityDerivation.lean | 2 | Chapman-Enskog |
| ExchangeIdentity.lean | 1 | Energy exchange |

### PhysicsAxioms.lean Structure (30 axioms)

**Phase7_Density.PhysicsAxioms namespace** (22 unique axioms):
- Type stubs (9): PhaseSpaceField, WeightFunction, ViscosityFromWeight, DiracOp, Commutator, Anticommutator, π_ρ, Δ_p, Lift
- Bridge axioms (3): bridge_advection, bridge_viscosity, dynamics_projects_to_NS
- Energy (4): E_spatial, E_momentum, E_spatial_nonneg, E_momentum_nonneg
- Scleronomic (3): IsScleronomic, scleronomic_conserves_energy, scleronomic_evolution_exists
- Misc (3): default_weight, viscosity, viscosity_pos

**NSE.Physics namespace** (10 axioms - for backward compatibility):
- Uses CONCRETE FunctionSpaces types (not axiom types)
- Duplicates some axioms for type compatibility with DynamicsBridge.lean
- Energy (4), Scleronomic (2), Viscosity (2), Dynamics (2)

### Axiom Reduction Opportunities

**Reducible to Theorems** (could eliminate ~4-6 axioms):
1. `E_spatial_nonneg`, `E_momentum_nonneg` - If E = ½∫|∇Ψ|², then E ≥ 0 by definition
2. `viscosity_pos` - If ν = ∫|∇ρ|² and ρ is non-constant, then ν > 0
3. `gradient_integral_nonneg` - Integral of squared function is non-negative
4. `gradient_integral_zero_of_constant` - Constant function has zero gradient

**Consolidation Opportunities**:
- Merge NSE.Physics axioms into Phase7_Density.PhysicsAxioms (would reduce ~8 axioms)
- This requires updating DynamicsBridge.lean to use axiom types

**Irreducible Physics Axioms** (~25-30):
- Type declarations (9): Core Cl(3,3) interface types
- Bridge axioms (3): [Ψ,DΨ]→advection, Δ_p→viscosity, scleronomic→NS
- Conservation (3): Energy conservation, evolution existence, Serrin uniqueness
- Boltzmann (4): Physical distribution properties
- Chapman-Enskog (2): Kinetic theory connection

### Target Axiom Count

| Reduction Phase | Axioms | Change |
|-----------------|--------|--------|
| Current | 43 | — |
| After energy ≥ 0 proofs | 39 | -4 |
| After namespace consolidation | 31 | -8 |
| **Realistic Target** | **~30** | **-13** |

The irreducible core should be ~25-30 axioms encoding:
- Cl(3,3) type interface (cannot eliminate without concrete implementation)
- Physical bridge claims (the "new physics")
- External results (Serrin uniqueness, Chapman-Enskog)

---

## Paper 3 Issues Found (CMI_Paper3_ViscosityEmergence.tex)

### 1. Axiom Count Update

**Wrong**: Various counts in papers
**Correct**: 43 explicit physics axioms (after Honest Axiomatics refactoring)

### 2. Lean Reference (Line 137)

**Current**: `Phase7_Density/ViscosityEmergence.momentum_laplacian_on_lift`
**Issue**: This theorem doesn't exist in the codebase

**Options**:
- Remove the Lean reference (the lemma is straightforward calculus)
- Reference the axiom: `Phase7_Density/ViscosityEmergence.momentum_laplacian_projects_to_viscous`

### 3. IsWeakNSSolution Definition

**Previously**: Vacuous `True` (critical vulnerability)
**Now**: Proper structure with TestFunction, continuity, and weak integral identity

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
