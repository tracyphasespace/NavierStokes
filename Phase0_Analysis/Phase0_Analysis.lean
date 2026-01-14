import Phase0_Analysis.PhaseSpaceField
import Phase0_Analysis.ProjectionRho
import Phase0_Analysis.Energy6D
import Phase0_Analysis.ConcreteInstantiation

/-!
# Phase 0: Analytic Layer - Module Aggregator

Import this file to pull in all Phase 0 analytic infrastructure.

## Purpose

This phase provides the **analytic bridge** between:
- The existing operator-algebraic framework (Phases 1-6)
- The infinite-dimensional function-space objects needed for Clay rigor

## Contents

* `PhaseSpaceField.lean` - Ψ : X → P → V as actual functions
* `ProjectionRho.lean` - Weighted projection πρ (bounded momentum probe)
* `Energy6D.lean` - Computed energy functional (not a record field)
* `ConcreteInstantiation.lean` - Concrete ℝ³ instantiation with proven lift

## Key Corrections from PDE Review

1. **Weighted projection**: Uniform average annihilates Δ_p; use non-constant ρ
2. **Computed energy**: Energy is an integral, not an assigned field
3. **Function spaces**: Ψ is infinite-dimensional, not a 6-tuple

## Main Definitions

* `PhaseSpaceField X P V` - Phase-space fields
* `πρ μP obs ρ Ψ` - Weighted momentum projection
* `energy_6d μX μP ops Vpot Ψ` - Computed energy functional
* `FieldDerivatives` - Six derivative operators with Schwarz commutation
* `IsScleronomicField` - D²Ψ = 0 in function-space form

## Claim Tags

| Tag | Description |
|-----|-------------|
| NS3.10 | PhaseSpaceField definition |
| NS3.11 | Weighted projection definition |
| NS3.12 | πρ definition |
| NS3.13-14 | πρ linearity |
| NS3.15 | πρ pointwise bound |
| NS3.16-17 | Energy functional definition |
| NS3.18-19 | Kinetic/potential decomposition |
| NS3.20-22 | Energy properties |
| NS3.23 | Scleronomic constraint |
| NS3.32-35 | Concrete instantiation (unconditional lift) |

## Status

With this infrastructure, Paper 3 provides:

1. **Lift Theorem** ✅: `πρ_liftField_eq` - proven in `ScleronomicLift_Analytic.lean`
2. **Concrete Lift** ✅: `scleronomic_lift_unconditional` - proven for ℝ³ with probability measures
3. **Energy Framework** ✅: `energy_6d` defined as computed integral
4. **Scleronomic Constraint** ✅: `IsScleronomicField` captures Δ_x Ψ = Δ_p Ψ
-/
