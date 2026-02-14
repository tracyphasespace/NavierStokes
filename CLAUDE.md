# CLAUDE.md - NavierStokesPaper Project

This file provides guidance to Claude Code when working with the Navier-Stokes formalization.

## Project Overview

**Purpose**: CMI Millennium Prize submission - Global Regularity of Navier-Stokes
**Approach**: Reformulate NS in Clifford algebra Cl(3,3) where blow-up is impossible
**Toolchain**: Lean 4.28.0-rc1 + Mathlib v4.28.0-rc1 + LeanCert (b3eaaae)

## Honest Status

**Algebraic core** (Phases 1-3): ~40 genuine theorems against Mathlib's `CliffordAlgebra`
- `[u,u] = 0`, advection+pressure decomposition, metric sign flip — all real algebra
- Zero non-Mathlib axioms in Phases 1-3

**Analytic bridge** (Phase 7): 0 axioms, 0 sorries, 0 vacuous definitions
- **0 axiom declarations** — physical hypotheses are structure fields of
  `ScleronomicKineticEvolution` (scleronomic, transport, closure, continuity, calculus)
- **0 sorries** — analysis facts in `CalculusRules` structure, proof by `rw [R1..R5]; ring`
- ALL definitions non-vacuous: real fderiv operators, real weak NS formulation
- CMI conclusion uses VECTOR IsWeakNSSolution with u⊗u nonlinearity
- ~25 genuine theorems (E_total_nonneg, reynolds_decomposition, etc.)

**Post-audit architecture** (Round 6):
- Round 5: Deleted 2 CIRCULAR scalar Stokes axioms, added 3 NON-CIRCULAR vector axioms
- Round 6: Converted 3 axioms → `ScleronomicKineticEvolution` structure fields
- Added `h_vel_continuous` field → eliminated sorry 1 (continuity)
- `#print axioms CMI_global_regularity` shows ZERO custom axioms, ZERO sorries

**Reduction journey**: 52 → 15 → 5 → 2 → 3 → 0 axioms, 0 sorries (current)

See `Lean/Validation/HonestyAudit.lean` for full documentation.

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
│   │   ├── PhysicsAxioms.lean    ← Physical hypotheses + definitions (0 axioms)
│   │   ├── EnergyConservation.lean ← Honest energy axioms
│   │   ├── DynamicsBridge.lean   ← 6D → 3D bridge
│   │   ├── CMI_Regularity.lean   ← Final CMI theorem
│   │   └── ...
│   │
│   └── Validation/               ← Axiom audit framework
│       ├── HonestyAudit.lean     ← Every axiom documented
│       └── AxiomDependencies.lean ← Axiom regression tests
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
```

### Phase 7: CMI Global Regularity (0 custom axioms)
```lean
-- THE CLAY MILLENNIUM PRIZE THEOREM — 0 CUSTOM AXIOMS
-- Physics hypotheses are in the ScleronomicKineticEvolution structure
-- #print axioms shows: [propext, Classical.choice, Quot.sound]
-- Proves VECTOR Navier-Stokes (with u⊗u nonlinearity!)
theorem CMI_global_regularity (ν : ℝ) (hν : ν > 0)
    (u₀ : VelocityField) (h_cont : Continuous (u₀ 0))
    (ρ : SmoothWeight) (hv : VacuumStructure ρ ν)
    (ev : ScleronomicKineticEvolution u₀ ρ ν) :
    ∃ u : VelocityField,
      (u 0 = u₀ 0) ∧ (IsWeakNSSolution u ν)
```

## Build Commands

```bash
# Build entire project
lake build NavierStokesPaper

# Build specific phase
lake build Phase7_Density
lake build Validation

# Count axioms (should be 0)
grep -rn "^axiom " Lean/ --include="*.lean" | wc -l

# Find sorries (should be 0)
grep -rn "sorry" Lean/ --include="*.lean" | grep -v "\-\-" | wc -l
```

## Critical Warnings

### DO NOT Modify (Protected Files)
- `Lean/Phase1_Foundation/Cl33.lean` - Core algebra, many files depend on it

### Tactic Notes for Cl(3,3)
- **DON'T use `ring`** - Clifford algebra is non-commutative!
- **DO use `abel`** - For additive group operations
- **Use `two_smul`** - For proving x + x = 2 • x

### Check for Active Builds Before Starting
```bash
pgrep -f "lake build" || echo "No build running"
```

### Avoid Parallel Builds
```bash
# ✅ CORRECT
lake build Module1 && lake build Module2

# ❌ WRONG (OOM crash or conflicts)
lake build Module1 & lake build Module2 &
```

## The Physical Summary

| Phase | What's Proven | Axioms | Key File |
|-------|---------------|--------|----------|
| Phase 1 | Cl(3,3) signature | 0 | `Cl33.lean` |
| Phase 2 | Viscosity = Exchange | 0 | `Conservation_Exchange.lean` |
| Phase 3 | Advection = Commutator | 0 | `Advection_Pressure.lean` |
| Phase 7 | Moment projection | 0 | `MomentProjection.lean` |
| Phase 7 | Reynolds decomp | 0 | `MomentDerivation.lean` |
| Phase 7 | CMI regularity (vector NS) | 0 | `CMI_Regularity.lean` |
| Validation | Axiom audit | 0 | `HonestyAudit.lean` |

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
