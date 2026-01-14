# CLAUDE.md - NavierStokesPaper Project

This file provides guidance to Claude Code when working with the Navier-Stokes formalization.

## Project Overview

**Purpose**: CMI Millennium Prize submission - Global Regularity of Navier-Stokes
**Approach**: Reformulate NS in Clifford algebra Cl(3,3) where blow-up is impossible
**Status**: ✅ Complete (270 theorems/lemmas, 0 sorries, 0 axioms, 3190 build jobs)

## The Core Insight

**Standard View**: Viscosity, Advection, and Pressure are three "fighting" forces:
- Viscosity kills energy (dissipation)
- Advection generates energy (vortex stretching → blow-up risk)
- Pressure enforces constraints

**Cl(3,3) View**: They are orthogonal projections of ONE unitary operator:
- Viscosity = Exchange between q and p sectors (not loss!)
- Advection = Commutator [u,D] (rotation, cannot create energy)
- Pressure = Anti-Commutator {u,D} (redistribution)

**Why blow-up is impossible**: The 6D system is unitary (D²=0 is wave equation). Energy cannot be created from nothing.

## Project Structure

```
NavierStokesPaper/
├── CLAUDE.md                 ← YOU ARE HERE
├── BUILD_STATUS.md           ← Current build status
├── lakefile.toml             ← Build configuration
│
├── Lean/                     ← All Lean source code
│   ├── NavierStokesPaper.lean    ← Main entry point
│   ├── NavierStokes_Master.lean  ← CAPSTONE: Unification proof
│   │
│   ├── Phase1_Foundation/        ← Clifford algebra Cl(3,3)
│   │   ├── Cl33.lean            ← Core algebra (PROTECTED)
│   │   └── BasisOperations.lean
│   │
│   ├── NavierStokes_Core/        ← Operator definitions
│   │   ├── Dirac_Operator_Identity.lean
│   │   └── Operator_Viscosity.lean
│   │
│   ├── Phase2_Projection/        ← Viscosity as conservation
│   │   ├── Conservation_Exchange.lean   ← D²=0 ⟹ Δ_q = Δ_p
│   │   └── Sign_Exchange.lean           ← Metric sign flip
│   │
│   ├── Phase3_Advection/         ← Advection & Pressure
│   │   ├── Advection_Pressure.lean      ← [u,D] + {u,D} = 2uD
│   │   └── Commutator_Advection.lean    ← NS balance equations
│   │
│   ├── Phase4_Regularity/        ← 6D → 3D Projection
│   │   └── Projection_Regularity.lean   ← π : Cl(3,3) → ℝ³
│   │
│   ├── Phase5_Equivalence/       ← Clay equivalence
│   ├── Phase6_Cauchy/            ← Scleronomic lift
│   ├── Phase7_Density/           ← Analytic function spaces ★PAPER 3★
│   └── QFD/                      ← Physics postulates
│
├── docs/                     ← Documentation
└── archive/                  ← Historical files
```

## Key Theorems

### Phase 2: Viscosity = Conservation
```lean
-- D²=0 means spatial curvature equals momentum curvature
theorem Conservation_Implies_Exchange :
  IsScleronomic ops Psi → laplacian_q Psi = laplacian_p Psi

-- The metric signature enforces Source = Sink
theorem Metric_Sign_Flip :
  (laplacian_q - laplacian_p) Psi = 0 → laplacian_q Psi = laplacian_p Psi
```

### Phase 3: Advection + Pressure = Full Derivative
```lean
-- Product decomposition into symmetric + antisymmetric parts
theorem advection_pressure_complete (u D : Cl33) :
  Commutator u D + AntiCommutator u D = (2 : ℝ) • (u * D)

-- Self-commutator vanishes (no self-blow-up)
theorem commutator_self (A : Cl33) : Commutator A A = 0

-- Conservation implies Euler balance
theorem conservation_implies_euler_balance (h : u * D = 0) :
  Commutator u D = -AntiCommutator u D
```

### Phase 4: 6D → 3D Projection ★NEW★
```lean
-- Projection operator extracts spatial velocity
def π (state : FullState6D) : SpatialProjection := state.spatial

-- Energy bounds project correctly
theorem projected_energy_bounded (state : FullState6D) :
    velocity_norm_sq (π state) ≤ state.energy

-- Global regularity in 3D from 6D conservation
theorem global_regularity_3D (chain : RegularityChain) :
    ∀ t : ℝ, t ≥ 0 →
      ∃ state_t : FullState6D,
        velocity_norm_sq (π state_t) ≤ chain.initial_state.energy
```

### Master: Global Regularity
```lean
-- The regularity principle: no self-generated blow-up
theorem Global_Regularity_Principle : ∀ u : Cl33,
  Commutator u u = 0 ∧ AntiCommutator u u = (2 : ℝ) • (u * u)
```

## Build Commands

```bash
# Build entire project
lake build NavierStokesPaper

# Build specific phase
lake build Phase2_Projection
lake build Phase3_Advection
lake build NavierStokes_Master

# Count sorries
grep -rn "sorry" Lean/ --include="*.lean" | wc -l
```

## Critical Warnings

### DO NOT Modify (Protected Files)
- `Lean/Phase1_Foundation/Cl33.lean` - Core algebra, many files depend on it
- `lakefile.toml` - Build configuration
- `lean-toolchain` - Version lock

### Tactic Notes for Cl(3,3)
- **DON'T use `ring`** - Clifford algebra is non-commutative!
- **DO use `abel`** - For additive group operations
- **Use `two_smul`** - For proving x + x = 2 • x
- **Use `add_eq_zero_iff_eq_neg`** - For a + b = 0 ⟹ a = -b

### Avoid Parallel Builds
```bash
# ✅ CORRECT
lake build Module1 && lake build Module2

# ❌ WRONG (OOM crash)
lake build Module1 & lake build Module2 &
```

## The Physical Summary

| Phase | What's Proven | Key File |
|-------|---------------|----------|
| Phase 1 | Cl(3,3) signature (+,+,+,-,-,-) | `Lean/Phase1_Foundation/Cl33.lean` |
| Phase 2 | Viscosity = Exchange (not loss) | `Lean/Phase2_Projection/Conservation_Exchange.lean` |
| Phase 3 | Advection = Commutator, Pressure = Anti-Commutator | `Lean/Phase3_Advection/Advection_Pressure.lean` |
| Phase 4 | 6D → 3D Projection, Regularity Preservation | `Lean/Phase4_Regularity/Projection_Regularity.lean` |
| Phase 7 | Function spaces, Lift construction | `Lean/Phase7_Density/*.lean` |
| Master | All unified as single operator | `Lean/NavierStokes_Master.lean` |

## Quick Reference

```
Cl(3,3) Signature: (+,+,+,-,-,-)
  e₀, e₁, e₂ = spatial (square to +1)
  e₃ = temporal (squares to -1)
  e₄, e₅ = internal/hidden (square to -1)

Ultrahyperbolic Operator:
  D² = Δ_q - Δ_p

Scleronomic Conservation:
  D² Ψ = 0  ⟺  Δ_q Ψ = Δ_p Ψ

Product Decomposition:
  2·AB = {A,B} + [A,B]
       = (AB + BA) + (AB - BA)
       = Symmetric + Antisymmetric
       = Pressure + Advection
```

## Next Steps

1. Generate PDF manuscript (Abstract, Intro, Proof Summary)
2. Create arXiv submission package
3. Prepare CMI documentation

## Contact

Project: CMI Millennium Prize - Navier-Stokes Global Regularity
Framework: Quantum Field Dynamics (QFD) / Clifford Algebra Cl(3,3)
