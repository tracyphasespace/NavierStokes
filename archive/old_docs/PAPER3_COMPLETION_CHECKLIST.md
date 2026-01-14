# Paper 3 Completion Checklist: Analytic Closure for CMI

**Date**: 2026-01-13
**Status**: IN PROGRESS - Critical corrections required

---

## CRITICAL CORRECTION: The Blow-Up Criterion

### ❌ CURRENT (WRONG) ARGUMENT

The current narrative states:
> "Blow-up requires |u| → ∞ ... But |u|² ≤ E(t) ≤ E(0) < ∞ ... Therefore QED"

**This is NOT the Clay regularity criterion.**

### ✅ CORRECT CRITERION

For Navier-Stokes, finite-time blow-up can occur via **loss of smoothness / derivative blow-up** while velocity remains bounded in weaker norms.

Paper 3 must control a **regularity norm**:
- Enstrophy: ‖ω‖²_{L²} = ‖∇×u‖²_{L²}
- Sobolev H¹: ‖u‖²_{H¹} = ‖u‖²_{L²} + ‖∇u‖²_{L²}
- BKM criterion: ∫₀ᵀ ‖ω(t)‖_{L^∞} dt < ∞

**Action Required**: Replace ALL instances of "bounded |u| implies no blow-up" with proper H¹/enstrophy arguments.

---

## Phase A: Audit and Re-Specification

### A.1 Ban Vacuity - Identify All Scaffolding

| File | Line | Current Form | Status |
|------|------|--------------|--------|
| LiftConstruction.lean | 126 | `lift_exists : ∃ Ψ, True` | ❌ Vacuous |
| LiftConstruction.lean | 115 | `pi_rho_lift_eq : ∀ x, True` | ❌ Vacuous |
| LiftConstruction.lean | 212 | `energy_bound : ∃ C > 0, True` | ❌ Vacuous |
| EnergyConservation.lean | 110 | `energy_conserved` via `simp; rfl` | ❌ Trivial |
| WeightedProjection.lean | 117 | `pi_rho_comm_dt : True` | ❌ Vacuous |
| WeightedProjection.lean | 141 | `pi_rho_bounded_Hk` with `trivial` | ❌ Incomplete |
| DynamicsEquivalence.lean | 111 | `dynamics_equivalence : True` | ❌ Vacuous |
| RegularityClosure.lean | 62-111 | All T1-T6 as `True` | ❌ Vacuous |

**Grep commands to find scaffolding:**
```bash
grep -rn ": True :=" Phase7_Density/ --include="*.lean"
grep -rn "by trivial" Phase7_Density/ --include="*.lean"
grep -rn "∃.*True" Phase7_Density/ --include="*.lean"
```

### A.2 Classify All Theorems

| Classification | Description | Examples |
|----------------|-------------|----------|
| **Algebraic** | Pure Cl(3,3) identities | `commutator_self`, `generator_squares_to_signature` |
| **Measure/Integration** | Bochner integrals, Fubini | `pi_rho_bounded_L2` |
| **Functional Analysis** | Sobolev bounds, operators | `projection_bounded_Hk`, `lift_energy_bound` |
| **PDE Equivalence** | NS from 6D evolution | `dynamics_equivalence` |
| **Regularity/Continuation** | BKM-type criteria | `regularity_from_H1_bound` |

---

## Phase B: Projection and Lift as Real Analysis

### B.1 Projection Boundedness

**Theorem Target**: `pi_rho_bounded_L2`
```lean
theorem pi_rho_bounded_L2 (ρ : SmoothWeight) (Ψ : PhaseSpaceField)
    (h_int : Integrable (fun z => ‖Ψ z‖²)) :
    ‖projectionWeighted ρ Ψ‖_{L²} ≤ C_ρ * ‖Ψ‖_{L²} := by
  -- Proof via Minkowski integral inequality
  sorry
```

**Proof Strategy**:
1. Apply Minkowski integral inequality
2. Use ρ normalization (∫ρ = 1 or bounded)
3. Conclude with norm estimate

**Status**: [ ] Not started

---

**Theorem Target**: `pi_rho_bounded_H1`
```lean
theorem pi_rho_bounded_H1 (ρ : SmoothWeight) (Ψ : RegularPhaseField 1) :
    ‖projectionWeighted ρ Ψ‖_{H¹} ≤ C_ρ * ‖Ψ‖_{H¹} := by
  -- Combine L² bound with derivative commutation
  sorry
```

**Status**: [ ] Not started

---

### B.2 Commutation with Derivatives

**Theorem Target**: `pi_rho_comm_dx`
```lean
theorem pi_rho_comm_dx (ρ : SmoothWeight) (Ψ : RegularPhaseField 1) (i : Fin 3) :
    ∂_{x_i} (projectionWeighted ρ Ψ) = projectionWeighted ρ (∂_{x_i} Ψ) := by
  -- Proof via Leibniz integral rule (differentiation under integral)
  -- Requires: Ψ and ∂Ψ integrable in p
  sorry
```

**Proof Strategy**:
1. Use `MeasureTheory.integral_deriv_swap` or equivalent
2. Verify integrability hypotheses
3. Use that ρ depends only on p (not x)

**Status**: [ ] Not started

---

### B.3 Right-Inverse Lift Theorem

**Theorem Target**: `projection_lift_eq` (REPLACES vacuous `lift_exists`)
```lean
theorem projection_lift_eq (ρ : SmoothWeight) (u : ScalarVelocityField)
    (h_norm : ∫ p, ρ.ρ p * liftWeight ρ p = 1) :
    projectionWeighted ρ (lift ρ u) = u := by
  -- Proof: factor u(x) out of integral, apply normalization
  ext x
  unfold projectionWeighted lift liftWeight embed
  -- ∫_p ρ(p) · (g(p) · u(x)) dp = u(x) · ∫_p ρ(p)·g(p) dp = u(x) · 1
  sorry
```

**Status**: [ ] Not started

---

**Theorem Target**: `lift_energy_bound` (REPLACES vacuous placeholder)
```lean
theorem lift_energy_bound (ρ : SmoothWeight) (u : VelocityField 1) :
    E_6D (lift ρ u) ≤ C_ρ * ‖u‖_{H¹}² := by
  -- Proof: separate x and p contributions
  -- E_6D = ∫∫ (|∇_x Ψ|² + |∇_p Ψ|²)
  -- For lift: ∇_x comes from u, ∇_p comes from weight
  sorry
```

**Status**: [ ] Not started

---

## Phase C: Energy Functional and Coercivity

### C.1 Define E_{6D} Properly

**Current Problem**: `gradXNormSq` and `gradPNormSq` return 0 (placeholders).

**Required Definition**:
```lean
/-- The 6D energy functional (kinetic part) -/
noncomputable def E_6D (Ψ : RegularPhaseField 1) : ℝ :=
  (1/2) * ∫ z : PhasePoint,
    (‖∂_x Ψ z‖² + ‖∂_p Ψ z‖²)
```

This requires actual derivative operators, not `id` placeholders.

**Status**: [ ] Not started

---

### C.2 Coercivity Lemma

**Theorem Target**: `energy_coercive`
```lean
theorem energy_coercive (Ψ : RegularPhaseField 1) :
    ‖∇_x Ψ‖²_{L²} ≤ C * E_6D Ψ := by
  -- E_6D includes |∇_x Ψ|², so this follows from definition
  sorry
```

**Status**: [ ] Not started

---

### C.3 Projection Transfers Bounds

**Theorem Target**: `projection_transfers_H1`
```lean
theorem projection_transfers_H1 (ρ : SmoothWeight) (Ψ : RegularPhaseField 1) :
    ‖projectionWeighted ρ Ψ‖_{H¹} ≤ C * E_6D Ψ := by
  -- Combine: projection bounded + energy coercive
  have h1 := pi_rho_bounded_H1 ρ Ψ
  have h2 := energy_coercive Ψ
  -- Chain the inequalities
  sorry
```

**Status**: [ ] Not started

---

## Phase D: Dynamics Equivalence (Make-or-Break)

### D.1 Specify 6D EOM Precisely

**Current Problem**: `Solves6D` is defined as `True`.

**Required Definition**:
```lean
/-- The 6D Hamiltonian evolution equation -/
def Solves6D (Ψ : ℝ → PhaseSpaceField) : Prop :=
  ∀ t, ∂_t (Ψ t) = hamiltonian6D (Ψ t)
  ∧ IsScleronomic (Ψ t)  -- D²Ψ = 0

/-- Hamiltonian from E_6D -/
def hamiltonian6D (Ψ : PhaseSpaceField) : PhaseSpaceField :=
  -- δE/δΨ* = D†D Ψ (plus potential term if any)
```

**Status**: [ ] Not started

---

### D.2 Prove Each NS Term Matches

**Theorem Target**: `advection_from_projection`
```lean
theorem advection_from_projection (ρ : SmoothWeight) (Ψ : Trajectory6D)
    (h_solves : Solves6D Ψ) :
    -- The advection term (u·∇)u comes from Clifford self-interaction
    advection_term (projectionWeighted ρ (Ψ t)) =
    projectionWeighted ρ (advection_6D (Ψ t)) := by
  sorry
```

**Status**: [ ] Not started

---

**Theorem Target**: `viscosity_from_projection`
```lean
theorem viscosity_from_projection (ρ : NonConstantWeight) (Ψ : Trajectory6D)
    (h_solves : Solves6D Ψ) :
    -- Viscosity νΔu comes from Δ_p via scleronomic + non-constant ρ
    ν * laplacian_x (projectionWeighted ρ.toSmoothWeight (Ψ t)) =
    projectionWeighted ρ.toSmoothWeight (viscosity_6D (Ψ t)) := by
  -- KEY: ρ must be non-constant to avoid annihilator trap
  sorry
```

**Status**: [ ] Not started

---

**Theorem Target**: `pressure_from_constraint`
```lean
theorem pressure_from_constraint (ρ : SmoothWeight) (Ψ : Trajectory6D)
    (h_solves : Solves6D Ψ) :
    -- Pressure gradient ∇p comes from incompressibility constraint
    ∃ p, grad p = projectionWeighted ρ (pressure_6D (Ψ t)) := by
  sorry
```

**Status**: [ ] Not started

---

### D.3 Full Dynamics Equivalence

**Theorem Target**: `dynamics_equivalence_NS` (REPLACES vacuous placeholder)
```lean
theorem dynamics_equivalence_NS (ρ : NonConstantWeight) (ν : ℝ)
    (Ψ : ℝ → PhaseSpaceField)
    (h_solves : Solves6D Ψ)
    (h_nu : ν = viscosity_from_weight ρ) :
    SolvesNS_weak (fun t => projectionWeighted ρ.toSmoothWeight (Ψ t)) ν := by
  -- Combine: advection + viscosity + pressure + div-free
  sorry
```

**Status**: [ ] Not started

---

## Phase E: Correct Regularity Criterion

### E.1 State Correct Continuation Criterion

**Theorem Target**: `continuation_from_H1_bound`
```lean
/-- Standard PDE: H¹ bound prevents finite-time blow-up -/
theorem continuation_from_H1_bound (u : ℝ → VelocityField 1) (T : ℝ)
    (h_NS : SolvesNS_weak u ν)
    (h_bound : ∀ t ∈ Icc 0 T, ‖u t‖_{H¹} < ∞) :
    ∃ ε > 0, ∀ t ∈ Icc 0 (T + ε), Smooth (u t) := by
  -- This is a standard PDE result (BKM-type)
  -- Can cite: Beale-Kato-Majda (1984), or Sobolev embedding + vorticity control
  sorry
```

**Status**: [ ] Not started

---

### E.2 Chain the Estimates

**Theorem Target**: `global_regularity_correct` (REPLACES incorrect narrative)
```lean
/-- MAIN THEOREM: Global H¹ regularity from 6D energy control -/
theorem global_regularity_correct (ρ : NonConstantWeight)
    (u₀ : VelocityField 1) (h_clay : ClayAdmissible u₀) :
    ∃ u : ℝ → VelocityField ∞,
      u 0 = u₀ ∧
      (∀ t ≥ 0, SolvesNS_weak u ν) ∧
      (∀ t ≥ 0, ‖u t‖_{H¹} ≤ C * ‖u₀‖_{H¹}) := by
  -- Step 1: Lift to 6D
  let Ψ₀ := lift ρ.toSmoothWeight u₀
  have h_lift : projectionWeighted ρ.toSmoothWeight Ψ₀ = u₀ := projection_lift_eq _ _ _

  -- Step 2: Evolve in 6D
  obtain ⟨Ψ, h_Ψ_solves⟩ := global_6D_evolution Ψ₀

  -- Step 3: Energy conservation
  have h_E : ∀ t, E_6D (Ψ t) = E_6D Ψ₀ := energy_conservation_real Ψ h_Ψ_solves

  -- Step 4: Coercivity + projection bound
  have h_H1 : ∀ t, ‖projectionWeighted ρ.toSmoothWeight (Ψ t)‖_{H¹} ≤ C * E_6D Ψ₀ := by
    intro t
    exact projection_transfers_H1 ρ.toSmoothWeight (Ψ t)

  -- Step 5: Dynamics equivalence
  have h_NS : SolvesNS_weak (fun t => projectionWeighted ρ.toSmoothWeight (Ψ t)) ν :=
    dynamics_equivalence_NS ρ ν Ψ h_Ψ_solves rfl

  -- Step 6: Uniform H¹ bound → global regularity
  have h_uniform : ∀ t ≥ 0, ‖u t‖_{H¹} ≤ C * ‖u₀‖_{H¹} := by
    intro t ht
    calc ‖u t‖_{H¹} ≤ C * E_6D Ψ₀ := h_H1 t
      _ ≤ C * C' * ‖u₀‖_{H¹}² := by apply lift_energy_bound
      _ ≤ C'' * ‖u₀‖_{H¹} := by sorry -- adjust constants

  sorry
```

**Status**: [ ] Not started

---

## Phase F: Documentation Updates

### F.1 Files to Update

| File | Required Changes |
|------|------------------|
| PROOF_DEPENDENCIES.md | Replace "bounded \|u\| implies QED" with H¹ criterion |
| BUILD_STATUS.md | Update theorem classifications |
| Complete_Lean_NSE.md | Rewrite regularity argument |
| CLAUDE.md | Update "Core Insight" to mention H¹ |

### F.2 Narrative Corrections

**DELETE** all instances of:
- "Blow-up requires |u| → ∞"
- "bounded velocity implies no blow-up"
- "|u|² ≤ E(0) therefore QED"

**REPLACE** with:
- "Blow-up requires loss of smoothness, detectable via ‖u‖_{H¹} → ∞"
- "bounded H¹ norm implies continuation of smooth solutions"
- "Energy coercivity gives ‖∇u‖_{L²} ≤ C·E_6D(0), therefore ‖u‖_{H¹} bounded"

---

## Acceptance Tests

### Test 1: No Vacuous Theorems
```bash
# Should return 0 matches
grep -rn "∃.*True" Phase7_Density/ --include="*.lean" | grep -v ".lake" | wc -l
# Expected: 0

grep -rn ": True :=" Phase7_Density/ --include="*.lean" | grep -v ".lake" | wc -l
# Expected: 0 (or minimal, with justification)
```

### Test 2: Correct Criterion in Documentation
```bash
# Should return 0 matches
grep -rn "blow-up requires.*|u|" . --include="*.md" | wc -l
# Expected: 0

# Should return multiple matches
grep -rn "H\^1\|enstrophy\|BKM" . --include="*.md" | wc -l
# Expected: > 5
```

### Test 3: Projection Lemmas Proven
```bash
# Check these theorems exist and are not trivial
grep -A5 "theorem pi_rho_bounded" Phase7_Density/WeightedProjection.lean
grep -A5 "theorem projection_lift_eq" Phase7_Density/LiftConstruction.lean
```

### Test 4: Build Still Passes
```bash
lake build NavierStokesPaper
# Expected: Success with 0 errors
```

---

## Priority Order

### IMMEDIATE (Before any other work)
1. [ ] Create this checklist as tracking document
2. [ ] Update PROOF_DEPENDENCIES.md to remove incorrect blow-up argument
3. [ ] Add note to BUILD_STATUS.md about scaffolding status

### HIGH PRIORITY (Phase B)
4. [ ] Prove `projection_lift_eq` (right-inverse)
5. [ ] Prove `pi_rho_bounded_L2` (L² boundedness)
6. [ ] Prove `pi_rho_comm_dx` (derivative commutation)

### MEDIUM PRIORITY (Phase C)
7. [ ] Define `E_6D` with actual gradients
8. [ ] Prove `energy_coercive`
9. [ ] Prove `projection_transfers_H1`

### LONGER TERM (Phase D-E)
10. [ ] Define `Solves6D` properly
11. [ ] Prove `dynamics_equivalence_NS`
12. [ ] State and prove `continuation_from_H1_bound`
13. [ ] Assemble `global_regularity_correct`

---

## What Can Be Paper vs What Must Be Lean

### MUST be Lean (operator/functional-analytic)
- Projection boundedness
- Derivative commutation
- Right-inverse lift
- Coercivity from energy definition
- Basic Sobolev inequalities

### CAN be paper (with citations)
- Full PDE existence/uniqueness theory
- BKM continuation criterion (cite Beale-Kato-Majda 1984)
- Leray-Hopf weak solution theory
- Strong solution regularity theory

### Honest Lean Scope
The Lean code verifies:
- The analytic machinery (projection, lift, energy)
- The algebraic structure (Cl(3,3), commutators)

The paper carries:
- PDE equivalence computations
- Standard continuation criteria
- Connection to established NS theory

---

## Summary: What Success Looks Like

Paper 3 is complete when:

1. ✅ **No vacuous claims** - Every theorem has substantive content
2. ✅ **Bounded projection** - π_ρ : H¹(ℝ³×𝕋³) → H¹(ℝ³) proven bounded
3. ✅ **Right-inverse lift** - π_ρ(Λu) = u proven (not "∃Ψ, True")
4. ✅ **Coercive energy** - E_6D controls ‖Ψ‖_{H¹}
5. ✅ **Dynamics equivalence** - 6D evolution projects to NS (proven or carefully cited)
6. ✅ **Correct criterion** - Regularity from H¹ bound, not just |u| bound

The honest claim becomes:
> "We have a phase-space embedding with a bounded projection and constructive right inverse. The conserved 6D functional controls the 3D H¹ norm. Therefore the standard derivative blow-up mechanism is ruled out."

---

**Next Action**: Begin with Phase A (audit) and the IMMEDIATE priority items.
