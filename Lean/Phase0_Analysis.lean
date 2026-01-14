import Phase0_Analysis.Phase0_Analysis

/-!
# Phase 0: Analytic Layer Root Import

This is the root import for Phase 0: Analytic Layer.
Import this to get all Phase 0 infrastructure.

## Contents

* `Phase0_Analysis.PhaseSpaceField` - Phase-space fields Ψ : X → P → V
* `Phase0_Analysis.ProjectionRho` - Weighted momentum projection πρ
* `Phase0_Analysis.Energy6D` - Computed energy functional

## Purpose

This phase provides the **analytic bridge** between:
- The operator-algebraic framework (Phases 1-6)
- The infinite-dimensional function-space objects needed for Clay rigor

## Key Definitions

* `PhaseSpaceField X P V` - Phase-space fields
* `VelocityField X W` - Velocity fields
* `πρ μP obs ρ Ψ` - Weighted momentum projection
* `energy_6d μX μP ops Vpot Ψ` - Computed energy functional
* `IsScleronomicField` - D²Ψ = 0 in function-space form
-/
