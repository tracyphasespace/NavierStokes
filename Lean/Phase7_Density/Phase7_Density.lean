import Phase7_Density.PhaseField
import Phase7_Density.WeightedProjection
import Phase7_Density.FunctionSpaces

/-!
# Phase 7 (Paper 3): Module Aggregator

Import this file to pull in all Phase 7 components.

## Live Modules

* `PhaseField.lean` - Type definitions (ScleronomicModel, KerD, projOnKer)
* `WeightedProjection.lean` - Corrected projection avoiding annihilator trap
* `FunctionSpaces.lean` - PhaseSpaceField, weighted projection, Sobolev spaces

## Critical Path (imported separately by CMI chain)

* `MomentProjection.lean` - Velocity/stress moments from phase-space distribution
* `EnergyConservation.lean` - 6D energy functional (0 axioms)
* `PhysicsAxioms.lean` - ScleronomicKineticEvolution + CalculusRules (0 axioms)
* `MomentDerivation.lean` - Transport → NS derivation (0 sorry)
* `DynamicsBridge.lean` - 6D → 3D bridge theorem
* `CMI_Regularity.lean` - Final CMI global regularity theorem

## Archived (vacuous/dead code moved to archive/)

* `AnalyticBridge.lean` - 7 vacuous `x = x := rfl` theorems
* `DiracOperator.lean` - 5 vacuous theorems + defs returning 0
* `DynamicsEquivalence.lean` - 5 vacuous theorems + NavierStokesOp := 0
* `RegularityClosure.lean` - 7 vacuous theorems
* `ViscosityDerivation.lean` - references deleted axioms
* `BoltzmannPhysics.lean` - dead chain
* `ViscosityEmergence.lean` - dead chain
* `ExchangeIdentity.lean` - references deleted axiom
* `LiftConstruction.lean` - placeholder constants
* `LiftTheorem.lean` - dead (only imported by this aggregator)
* `GradeDecomposition.lean` - UnityTheorem with n=n fields
-/
