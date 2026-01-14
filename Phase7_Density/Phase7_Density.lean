import Phase7_Density.PhaseField
import Phase7_Density.LiftTheorem
import Phase7_Density.WeightedProjection
import Phase7_Density.AnalyticBridge
import Phase7_Density.FunctionSpaces
import Phase7_Density.DiracOperator
import Phase7_Density.DynamicsEquivalence
import Phase7_Density.RegularityClosure

/-!
# Phase 7 (Paper 3): Module Aggregator

Import this file to pull in all Phase 7 components.

## Contents

### Abstract Interface Layer
* `PhaseField.lean` - Type definitions (ScleronomicModel, KerD, projOnKer)
* `LiftTheorem.lean` - Main theorem (closed + dense ⟹ lift exists)
* `WeightedProjection.lean` - Corrected projection avoiding annihilator trap
* `AnalyticBridge.lean` - The six theorems needed for Clay closure

### Concrete Function Space Layer
* `FunctionSpaces.lean` - PhaseSpaceField, weighted projection, Sobolev spaces
* `DiracOperator.lean` - Cl(3,3) Dirac operator on function spaces
* `DynamicsEquivalence.lean` - 6D dynamics ⟹ NS dynamics (T5)
* `RegularityClosure.lean` - Complete argument assembly

## Main Results

* `scleronomic_lift_from_density`: The core lift theorem
* `lift_exists_for_all_admissible`: Universal statement for admissible data
* `Paper3Checklist`: The six-theorem structure for full Clay closure
* `global_regularity_from_6D_control`: Final regularity theorem

## Mathematical Summary

Paper 3 reduces the lift problem to two functional analysis hypotheses:

1. **Closed Range**: `IsClosed (range projOnKer)`
2. **Density**: `AdmissibleSet ⊆ closure (range projOnKer)`

### Key Corrections (from PDE analysis review)

1. **Weighted projection**: Uniform average annihilates Δ_p; use ρ-weighted
2. **H¹ is supercritical**: H^{1/2} is critical; H¹ more than suffices
3. **L² control needed**: Coercivity requires mass term or conserved charge

### Six-Theorem Checklist

| # | Statement | Status |
|---|-----------|--------|
| T1 | Projection bounded: ‖π_ρ Ψ‖_{H¹} ≤ C ‖Ψ‖_{H¹} | Structure |
| T2 | D² identity: D²Ψ = 0 ⟹ Δ_x Ψ = Δ_p Ψ | Structure |
| T3 | Energy conserved: E(Ψ(t)) = E(Ψ₀) | Structure |
| T4 | Energy coercive: E(Ψ) ≥ c ‖Ψ‖² | Structure |
| T5 | Dynamics equivalence: π_ρ(Ψ) solves NS | CRITICAL |
| T6 | Regularity criterion: 6D bounded ⟹ 3D regular | Structure |
-/
