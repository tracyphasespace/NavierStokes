# CMI Navier-Stokes: Complete Dependency DAG

## Visual Proof Chain

```
                    ┌─────────────────────────────────────┐
                    │     PHASE 1: FOUNDATION             │
                    └─────────────────────────────────────┘
                                    │
        ┌───────────────────────────┼───────────────────────────┐
        ▼                           ▼                           ▼
┌───────────────┐         ┌─────────────────┐         ┌─────────────────┐
│ Def_Cl33      │         │ Def_Signature   │         │ Def_Quadratic   │
│ Algebra       │         │ (+,+,+,-,-,-)   │         │ Form Q33        │
│ [Cl33Core:87] │         │ [Cl33Core:23]   │         │ [Cl33Core:48]   │
└───────┬───────┘         └────────┬────────┘         └────────┬────────┘
        │                          │                           │
        └──────────────────────────┼───────────────────────────┘
                                   ▼
                    ┌──────────────────────────┐
                    │ Thm_Generator_Squares    │
                    │ eᵢ² = σᵢ                 │
                    │ [Cl33Core:72]            │
                    └────────────┬─────────────┘
                                 │
        ┌────────────────────────┼────────────────────────┐
        ▼                        ▼                        ▼
┌───────────────┐    ┌────────────────────┐    ┌─────────────────┐
│ Thm_Anticomm  │    │ Thm_Spacelike_Pos  │    │ Thm_Timelike_Neg│
│ eᵢeⱼ = -eⱼeᵢ │    │ e₀²=e₁²=e₂²=+1    │    │ e₃²=e₄²=e₅²=-1 │
│ [Cl33Core:90] │    │ [Cl33Core:110]     │    │ [Cl33Core:117]  │
└───────┬───────┘    └─────────┬──────────┘    └────────┬────────┘
        │                      │                        │
        └──────────────────────┼────────────────────────┘
                               ▼
                ┌──────────────────────────────┐
                │ Thm_Signature_Trace_Zero     │
                │ Σᵢ σᵢ = 3(+1) + 3(-1) = 0    │
                │ [Cl33Core:130]               │
                │ **CRITICAL FOR REGULARITY**  │
                └──────────────┬───────────────┘
                               │
                    ┌──────────────────────────────────────┐
                    │     PHASE 2: OPERATORS               │
                    └──────────────────────────────────────┘
                               │
        ┌──────────────────────┼──────────────────────┐
        ▼                      ▼                      ▼
┌───────────────┐    ┌─────────────────┐    ┌─────────────────┐
│ Def_Nabla     │    │ Def_Grade_Proj  │    │ Def_Wedge_Dot   │
│ ∇ = Σ eᵢ∂ᵢ   │    │ ⟨·⟩₀, ⟨·⟩₁, ⟨·⟩₂│    │ a∧b, a·b        │
│ [VecDeriv:25] │    │ [GradeProj:20]  │    │ [GradeProj:45]  │
└───────┬───────┘    └────────┬────────┘    └────────┬────────┘
        │                     │                      │
        └─────────────────────┼──────────────────────┘
                              ▼
                ┌──────────────────────────────┐
                │ Def_Dirac_Operator           │
                │ ∂̸ = ∇ (as Cl(3,3) element)   │
                │ [DiracOp:30]                 │
                └──────────────┬───────────────┘
                               │
                    ┌──────────────────────────────────────┐
                    │     PHASE 3: ISOMORPHISM             │
                    │     **THE BOSS FIGHT**               │
                    └──────────────────────────────────────┘
                               │
        ┌──────────────────────┼──────────────────────┐
        ▼                      ▼                      ▼
┌───────────────┐    ┌─────────────────┐    ┌─────────────────┐
│ Lem_Grad_Sq   │    │ Lem_Mixed_Grad  │    │ Lem_Vec_Prod    │
│ ∇²=∇·∇+∇∧∇   │    │ ∂ᵢ∂ⱼ coupling   │    │ vw=v·w+v∧w      │
│ [LaplSplit:35]│    │ [LaplSplit:60]  │    │ [Advect:25]     │
└───────┬───────┘    └────────┬────────┘    └────────┬────────┘
        │                     │                      │
        └─────────────────────┼──────────────────────┘
                              ▼
                ┌──────────────────────────────┐
                │ **THEOREM: Viscosity_Emerge**│
                │                              │
                │ ⟨∇², v⟩_bivector = ν∇²_spat v│
                │                              │
                │ [ViscEmerg:95]               │
                │ **THIS IS THE KEY PROOF**    │
                └──────────────┬───────────────┘
                               │
                ┌──────────────┴───────────────┐
                ▼                              ▼
    ┌────────────────────┐        ┌────────────────────┐
    │ Lem_Advection      │        │ Lem_Pressure       │
    │ ⟨v∇v⟩₀ = (v·∇)v   │        │ ⟨∇p⟩₁ = grad(p)   │
    │ [Advect:55]        │        │ [Advect:70]        │
    └─────────┬──────────┘        └─────────┬──────────┘
              │                             │
              └──────────────┬──────────────┘
                             ▼
                ┌──────────────────────────────┐
                │ **THEOREM: NS_From_Clifford**│
                │                              │
                │ ∂ₜv + (v·∇)v = ν∇²v - ∇p     │
                │                              │
                │ [ViscEmerg:145]              │
                └──────────────┬───────────────┘
                               │
                    ┌──────────────────────────────────────┐
                    │     PHASE 4: REGULARITY              │
                    └──────────────────────────────────────┘
                               │
        ┌──────────────────────┼──────────────────────┐
        ▼                      ▼                      ▼
┌───────────────┐    ┌─────────────────┐    ┌─────────────────┐
│ Def_Symplect  │    │ Lem_Dirac_Skew  │    │ Lem_Trace_Zero  │
│ ω = Σ eᵢ∧eᵢ₊₃│    │ ∂̸ᵀ = -∂̸        │    │ Tr(∂̸) = 0      │
│ [Symplect:20] │    │ [Symplect:45]   │    │ [Symplect:60]   │
└───────┬───────┘    └────────┬────────┘    └────────┬────────┘
        │                     │                      │
        └─────────────────────┼──────────────────────┘
                              ▼
                ┌──────────────────────────────┐
                │ **THEOREM: Liouville_Inv**   │
                │                              │
                │ Tr(∂̸) = 0 ⟹ dω⁶/dt = 0     │
                │ (Volume preserved)           │
                │ [Liouville:40]               │
                └──────────────┬───────────────┘
                               │
                               ▼
                ┌──────────────────────────────┐
                │ **THEOREM: Energy_Bounded**  │
                │                              │
                │ ‖v‖² ≤ E₀ (conserved)        │
                │ [GlobalEx:35]                │
                └──────────────┬───────────────┘
                               │
                               ▼
                ┌──────────────────────────────┐
                │ **THEOREM: Global_Existence**│
                │                              │
                │ Energy bounded +             │
                │ Volume preserved             │
                │ ⟹ Density bounded           │
                │ ⟹ No finite-time blow-up    │
                │                              │
                │ [GlobalEx:80]                │
                │ **REGULARITY ESTABLISHED**   │
                └──────────────────────────────┘
```

## File Dependencies (Import Order)

```
Phase1_Foundation/
├── Cl33Core.lean           [NO DEPS - Base]
├── SplitBasis.lean         [imports Cl33Core]
└── Pseudoscalar.lean       [imports Cl33Core, SplitBasis]

Phase2_Operators/
├── GradeProjection.lean    [imports Phase1/*]
├── VectorDerivative.lean   [imports Phase1/*, GradeProjection]
└── DiracOperator.lean      [imports VectorDerivative]

Phase3_Isomorphism/
├── LaplacianSplit.lean     [imports Phase2/*]
├── ViscosityEmergence.lean [imports LaplacianSplit] **BOSS**
└── AdvectionRecovery.lean  [imports LaplacianSplit]

Phase4_Regularity/
├── SymplecticForm.lean     [imports Phase1/*, Phase2/*]
├── LiouvilleInvariant.lean [imports SymplecticForm]
└── GlobalExistence.lean    [imports Phase3/*, Liouville]

NavierStokes_Complete.lean  [imports ALL above]
```

## Critical Path (Minimum for CMI)

The absolutely essential chain (12 theorems):

```
1. Def_Cl33_Algebra         [Foundation]
2. Def_Signature33          [Foundation]
3. Thm_Generator_Squares    [Foundation]
4. Thm_Anticommute          [Foundation]
5. Thm_Signature_Trace_Zero [Foundation] ← KEY
6. Def_Vector_Derivative    [Operators]
7. Lem_Grad_Squared         [Isomorphism]
8. Thm_Viscosity_Emergence  [Isomorphism] ← BOSS FIGHT
9. Lem_Advection_Recovery   [Isomorphism]
10. Thm_Liouville_Invariant [Regularity]
11. Thm_Energy_Bounded      [Regularity]
12. Thm_Global_Existence    [Regularity] ← FINAL
```

## Sorry Status

| Phase | File | Sorries | Status |
|-------|------|---------|--------|
| 1 | Cl33Core.lean | 0 | ✅ Complete |
| 1 | SplitBasis.lean | - | Not started |
| 1 | Pseudoscalar.lean | - | Not started |
| 2 | GradeProjection.lean | - | Partial (from QFD) |
| 2 | VectorDerivative.lean | - | Not started |
| 2 | DiracOperator.lean | - | Partial (from QFD) |
| 3 | LaplacianSplit.lean | - | Not started |
| 3 | **ViscosityEmergence.lean** | **4** | **THE GAP** |
| 3 | AdvectionRecovery.lean | - | Not started |
| 4 | SymplecticForm.lean | - | Not started |
| 4 | LiouvilleInvariant.lean | - | Not started |
| 4 | GlobalExistence.lean | - | Not started |

## Target: Zero Sorries

To achieve CMI submission readiness:
1. ✅ Phase 1: Extract and verify from QFD/GA/
2. ⏳ Phase 2: Complete operator definitions
3. ❌ Phase 3: **Prove ViscosityEmergence** (critical)
4. ❌ Phase 4: Develop regularity chain

Estimated work:
- Phase 1-2: Days (mostly extraction)
- Phase 3: Weeks (requires careful algebra)
- Phase 4: Weeks (requires functional analysis)
