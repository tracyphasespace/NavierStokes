# NavierStokesPaper File Categorization

**Date**: 2026-01-14
**Purpose**: Identify files needed for CMI NS proof vs QFD physics framework

---

## Legend

| Symbol | Meaning |
|--------|---------|
| **NS** | Required for Navier-Stokes CMI proof |
| **QFD** | QFD particle physics (separate project) |
| **SHARED** | Cl(3,3) algebra used by both |

---

## NS CORE (Required for CMI Proof)

These files form the complete NS regularity proof chain:

### Phase 1: Clifford Algebra Foundation
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase1_Foundation/Cl33.lean` | **SHARED** | Cl(3,3) definition - used by both NS and QFD |
| `Lean/Phase1_Foundation/BasisOperations.lean` | **NS** | Basis ops for D² |
| `Lean/Phase1_Foundation/BasisProducts.lean` | **NS** | Basis products |
| `Lean/Phase1_Foundation/BasisReduction.lean` | **NS** | Basis reduction |
| `Lean/Phase1_Foundation/Cl33Instances.lean` | **NS** | Type instances |
| `Lean/Phase1_Foundation/HodgeDual.lean` | **NS** | Hodge duality |
| `Lean/Phase1_Foundation/PhaseCentralizer.lean` | **NS** | Phase centralizer |

### NavierStokes Core Operators
| File | Status | Notes |
|------|--------|-------|
| `Lean/NavierStokes_Core/Dirac_Operator_Identity.lean` | **NS** | D² = Δ_q - Δ_p |
| `Lean/NavierStokes_Core/Operator_Viscosity.lean` | **NS** | Viscosity operator |
| `Lean/NavierStokes_Core/Nonlinear_Emergence.lean` | **NS** | Nonlinear terms |
| `Lean/NavierStokes_Core/Lemma_Viscosity_Emergence.lean` | **NS** | Viscosity lemma |

### Phase 2: Viscosity = Conservation
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase2_Projection/Conservation_Exchange.lean` | **NS** | D²=0 ⟹ Δ_q = Δ_p |
| `Lean/Phase2_Projection/Sign_Exchange.lean` | **NS** | Metric sign flip |

### Phase 3: Advection + Pressure
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase3_Advection/Advection_Pressure.lean` | **NS** | [u,D] + {u,D} = 2uD |
| `Lean/Phase3_Advection/Commutator_Advection.lean` | **NS** | Commutator identity |

### Phase 4: Regularity
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase4_Regularity/GlobalExistence.lean` | **NS** | 6D existence |
| `Lean/Phase4_Regularity/Projection_Regularity.lean` | **NS** | π: 6D → 3D |
| `Lean/Phase4_Regularity/SymplecticForm.lean` | **NS** | Symplectic structure |
| `Lean/Phase4_Regularity/LiouvilleInvariant.lean` | **NS** | Liouville theorem |

### Phase 5: Clay Equivalence
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase5_Equivalence/ClayEquivalence.lean` | **NS** | CMI problem mapping |
| `Lean/Phase5_Equivalence/NoetherCompliance.lean` | **NS** | Noether theorem |
| `Lean/Phase5_Equivalence/Imports.lean` | **NS** | Import aggregation |

### Phase 6: Scleronomic Lift
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase6_Cauchy/ScleronomicLift.lean` | **NS** | Lift existence |
| `Lean/Phase6_Cauchy/ScleronomicLift_Analytic.lean` | **NS** | Analytic properties |

### Phase 7: Function Spaces (Paper 3)
| File | Status | Notes |
|------|--------|-------|
| `Lean/Phase7_Density/FunctionSpaces.lean` | **NS** | H^k, L² spaces |
| `Lean/Phase7_Density/WeightedProjection.lean` | **NS** | π_ρ operator |
| `Lean/Phase7_Density/LiftConstruction.lean` | **NS** | Λ lift operator |
| `Lean/Phase7_Density/EnergyConservation.lean` | **NS** | E_{6D} conserved |
| `Lean/Phase7_Density/DiracOperator.lean` | **NS** | D operator |
| `Lean/Phase7_Density/PhaseField.lean` | **NS** | Phase space fields |
| `Lean/Phase7_Density/LiftTheorem.lean` | **NS** | π_ρ(Λu) = u |
| `Lean/Phase7_Density/AnalyticBridge.lean` | **NS** | Analytic bridge |
| `Lean/Phase7_Density/DynamicsEquivalence.lean` | **NS** | Dynamics equivalence |
| `Lean/Phase7_Density/RegularityClosure.lean` | **NS** | Regularity closure |
| `Lean/Phase7_Density/Phase7_Density.lean` | **NS** | Module index |

### Master Unification
| File | Status | Notes |
|------|--------|-------|
| `Lean/NavierStokes_Master.lean` | **NS** | Capstone theorem |
| `Lean/NavierStokesPaper.lean` | **NS** | Root module |

### Index Files (NS)
| File | Status |
|------|--------|
| `Lean/Phase0_Analysis.lean` | **NS** |
| `Lean/Phase1_Foundation.lean` | **NS** |
| `Lean/Phase2_Projection.lean` | **NS** |
| `Lean/Phase3_Advection.lean` | **NS** |
| `Lean/Phase4_Regularity.lean` | **NS** |
| `Lean/Phase5_Equivalence.lean` | **NS** |
| `Lean/Phase6_Cauchy.lean` | **NS** |
| `Lean/Phase7_Density.lean` | **NS** |
| `Lean/NavierStokes_Core.lean` | **NS** |

---

## SUGGESTED FOR REMOVAL (QFD Physics)

These files are real Lean proofs but belong in a separate QFD library:

### QFD Vacuum Theory
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/QFD/Charge/Vacuum.lean` | Time refraction, polarity | QED, not fluid dynamics |
| `Lean/QFD/Vacuum/VacuumParameters.lean` | β, ξ, proton mass | QED matching, not NS |

### QFD Soliton/Particle Physics
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/QFD/Soliton/MassEnergyCore.lean` | Soliton mass-energy | Particle physics |
| `Lean/QFD/Soliton/TopologicalCore.lean` | Topological charge | Particle topology |
| `Lean/QFD/Soliton/TopologicalStability.lean` | Soliton stability | Particle stability |
| `Lean/QFD/Soliton/Quantization.lean` | Charge quantization | QED |
| `Lean/QFD/Soliton/HardWall.lean` | Hard wall BC | Particle confinement |
| `Lean/QFD/Soliton/GaussianMoments.lean` | Gaussian moments | Particle wavefunctions |

### QFD Lepton Sector
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/QFD/Lepton/Topology.lean` | Lepton topology | Particle physics |
| `Lean/QFD/Lepton/VortexStability.lean` | Vortex stability | Particle vortices |
| `Lean/QFD/Lepton/IsomerCore.lean` | Isomer structure | Particle isomers |

### QFD Electron/Hydrogen
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/QFD/Electron/HillVortex.lean` | Hill vortex model | Electron model |
| `Lean/QFD/Hydrogen/PhotonSoliton.lean` | Photon soliton | QED photon |
| `Lean/QFD/Hydrogen/PhotonSolitonStable.lean` | Photon stability | QED |
| `Lean/QFD/Hydrogen/PhotonSolitonEmergentConstants.lean` | ℏ, c derivation | QED constants |

### QFD Physics Postulates
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/QFD/Physics/Postulates.lean` | QFD postulates | General QFD framework |

### Misplaced Files in Phase Directories
| File | Content | Why Not NS |
|------|---------|------------|
| `Lean/Phase3_Isomorphism/VacuumHydrodynamics.lean` | c = √(β/ρ), ℏ derivation | QED, not NS |

### Duplicate/Redundant
| File | Notes |
|------|-------|
| `Lean/QFD/GA/Cl33.lean` | Duplicate of Phase1_Foundation/Cl33.lean |

### Index Files to Remove
| File | Notes |
|------|-------|
| `Lean/QFD.lean` | Imports all QFD physics |

---

## BORDERLINE CASES (Review Needed)

| File | Content | Decision |
|------|---------|----------|
| `Lean/Phase0_Analysis/*.lean` | Phase space fields | Likely **NS** - supports Paper 3 |
| `Lean/Phase2_Operators/*.lean` | Dirac operators | Likely **NS** - supports D² |
| `Lean/Phase3_Isomorphism/CliffordBeltrami.lean` | Clifford-Beltrami | Likely **NS** |
| `Lean/Phase3_Isomorphism/LaplacianSplit.lean` | Laplacian split | Likely **NS** |
| `Lean/Phase3_Isomorphism/AdvectionRecovery.lean` | Advection recovery | Likely **NS** |
| `Lean/Phase3_Isomorphism/ViscosityEmergence.lean` | Viscosity emergence | Likely **NS** |

---

## Summary

| Category | Count |
|----------|-------|
| **NS Core** | ~50 files |
| **QFD (Remove)** | ~18 files |
| **Borderline** | ~10 files |

---

## Recommended Actions

1. **Create `suggested_for_removal/QFD/`** directory
2. **Move all QFD files** (listed above) to that directory
3. **Remove QFD imports** from lakefile.toml
4. **Test NS build** to ensure no dependencies broken
5. **Later**: Move QFD files to separate `QFD_Library/` project

---

## Namespace Cleanup Note

The NS proof currently uses `namespace QFD.GA` and `namespace QFD.Phase*`.
After cleanup, consider renaming to:
- `NSE.Algebra` (instead of QFD.GA)
- `NSE.Phase2` (instead of QFD.Phase2)
- etc.

This would fully decouple the NS proof from the QFD physics framework.
