# CMI Proof Gap Analysis: Attack Vectors and Missing Proofs

## Executive Summary

The current formalization has **30 physics axioms** and **0 sorries**. However, several axioms are **reducible** (should be theorems), and some key connections are **placeholders** (defined as `True`). Skeptics will target these.

---

## CRITICAL: Placeholder Definitions (Immediate Fix Required)

### 1. Weak/Strong NS Solution Definitions

**Location**: `Phase7_Density/PhysicsAxioms.lean:58-62`

```lean
def IsWeakNSSolution (u : ℝ → ScalarVelocityField) (ν : ℝ) : Prop := True
def IsStrongNSSolution (u : ℝ → ScalarVelocityField) (ν : ℝ) : Prop := IsWeakNSSolution u ν ∧ True
```

**Problem**: These are vacuously true! The entire CMI theorem rests on showing `u` is an NS solution, but the definition accepts *any* function.

**Fix Required**: Define weak NS solution properly:
```lean
def IsWeakNSSolution (u : ℝ → VelocityField) (ν : ℝ) : Prop :=
  ∀ φ : TestFunction, ∀ t : ℝ,
    ∫ u(t) · ∂_t φ + ∫ (u ⊗ u) : ∇φ = -ν ∫ ∇u : ∇φ
```

**Skeptic Attack**: "Your theorem proves nothing—any function satisfies `IsWeakNSSolution`."

---

### 2. The Dynamics Bridge Axiom

**Location**: `Phase7_Density/PhysicsAxioms.lean` (axiom `dynamics_projects_to_NS`)

**Current Status**: AXIOM (not proven)

**What It Claims**: If Ψ evolves scleronomically, then π(Ψ) satisfies NS.

**This is THE critical claim**. Everything else is scaffolding for this.

**What Would Be Needed to Prove It**:
1. Show ∂_t(πΨ) = π(∂_t Ψ) (projection commutes with time derivative)
2. Show π(Δ_p Ψ) = ν·Δ(πΨ) (momentum Laplacian → viscous term) ← Partially done
3. Show π([Ψ, D]) = (u·∇)u (commutator → advection) ← NOT PROVEN
4. Show π({Ψ, D}) = ∇p (anticommutator → pressure) ← NOT PROVEN

**Skeptic Attack**: "You've axiomatized exactly what you're trying to prove."

---

## HIGH PRIORITY: Reducible Axioms

### Category A: Laplacians (2 axioms → 0 axioms)

**Current**:
```lean
axiom laplacian_x : SpatialLaplacian
axiom laplacian_p : MomentumLaplacian
```

**Should Be**: Definitions, not axioms. The Laplacian is just Σ ∂²/∂x_i².

**Fix**:
```lean
def laplacian_x (f : ℝ³ → ℝ) : ℝ³ → ℝ := 
  fun x => ∂²f/∂x₁² + ∂²f/∂x₂² + ∂²f/∂x₃²
```

**Axiom Reduction**: 30 → 28

---

### Category B: Energy Non-negativity (2 axioms → 0 axioms)

**Current**:
```lean
axiom E_spatial_nonneg : E_spatial Ψ ≥ 0
axiom E_momentum_nonneg : E_momentum Ψ ≥ 0
```

**Should Be**: Theorems. If E = ½∫|∇Ψ|², then E ≥ 0 by definition (integral of non-negative function).

**Fix**:
```lean
theorem E_spatial_nonneg (Ψ : PhaseSpaceField) : E_spatial Ψ ≥ 0 := by
  unfold E_spatial
  apply integral_nonneg
  intro x
  exact sq_nonneg _
```

**Axiom Reduction**: 28 → 26

---

### Category C: Lift Right Inverse (1 axiom → theorem)

**Current**:
```lean
axiom lift_right_inverse : π_ρ ∘ Λ_ρ = id
```

**Should Be**: Provable from ∫ρ² = 1 normalization.

**Proof Sketch**:
```
(π_ρ ∘ Λ_ρ)(u)(x) = ∫ ρ(p) · [ρ(p) · u(x)] dp
                   = u(x) · ∫ ρ(p)² dp
                   = u(x) · 1
                   = u(x)
```

**Status**: This IS proven in `LiftConstruction.pi_rho_lift_eq` but requires `IntegralCoercionHolds` hypothesis. Should be unconditional.

**Axiom Reduction**: 26 → 25

---

### Category F: Viscosity Formula (1 axiom → theorem)

**Current**:
```lean
axiom viscosity_from_projection : ν = (1/Vol) * ∫|∇ρ|²
```

**Should Be**: Derivable from integration by parts.

**Proof**:
```
π(Δ_p Ψ) = ∫ ρ(p) · Δ_p[ρ(p) · u(x)] dp
         = u(x) · ∫ ρ · Δρ dp
         = u(x) · (-∫ |∇ρ|² dp)   [integration by parts]
         = -ν · u(x)
```

**Status**: Partially done in `ViscosityEmergence.lean` but the IBP step may be axiomatized.

---

## MEDIUM PRIORITY: Structural Gaps

### 1. Advection Term: [u, D] → (u·∇)u

**Current Status**: Algebraic identities proven, but connection to NS advection is "physical interpretation."

**What's Missing**:
```lean
theorem commutator_projects_to_advection :
  π([Ψ, D]) = (πΨ · ∇)(πΨ)
```

**Difficulty**: HIGH. Requires showing the Clifford commutator structure maps to the nonlinear advection term under projection.

**Possible Approach**: 
- Define velocity as v^i = π(e_i · Ψ)
- Show [Ψ, D] involves grade-1 × grade-1 products
- Show projection extracts the symmetric (advection) part

---

### 2. Pressure Term: {u, D} → ∇p

**Current Status**: Anticommutator defined, connection to pressure not proven.

**What's Missing**:
```lean
theorem anticommutator_projects_to_pressure :
  ∃ p, π({Ψ, D}) = ∇p ∧ div(πΨ) = 0 → Δp = -div((πΨ·∇)πΨ)
```

**Difficulty**: MEDIUM. Pressure in NS is determined by the divergence-free constraint.

---

### 3. Evolution Persistence of Tensor Product Form

**Current Claim**: Start with Ψ₀ = ρ(p)·u₀(x), evolve scleronomically, project back.

**Gap**: Does scleronomic evolution preserve the tensor product structure?

If Ψ(t) = e^{itD}Ψ₀, is Ψ(t) still of the form ρ(p)·u(t,x)?

**Answer**: NO, in general. The evolution mixes x and p dependence.

**Why This Matters**: The projection π(Ψ(t)) averages over this mixing—this is where viscosity "emerges."

**What's Missing**: Proof that the averaged projection still satisfies NS, even when Ψ(t) is no longer separable.

---

## LOWER PRIORITY: Physics Interface Axioms

These axioms encode standard physics and are unlikely to be challenged:

### Reasonable to Keep as Axioms:
- `scleronomic_conserves_energy` (Noether's theorem)
- `scleronomic_evolution_exists` (Stone's theorem for self-adjoint operators)
- `NS_uniqueness` (Serrin's theorem—external result)
- `our_formula_matches_CE` (Chapman-Enskog connection—physics claim)

### Could Be Proven with More Work:
- `boltzmann_pointwise_bound` (ρ ≤ 1 follows from normalization + smoothness)
- `boltzmann_gradient_integral` (explicit Gaussian integral computation)
- `energy_coercivity` (Poincaré inequality—standard but technical)

---

## Attack Vector Summary

| Attack | Severity | Current Defense | Fix |
|--------|----------|-----------------|-----|
| "NS solution is vacuous `True`" | **CRITICAL** | None | Define properly |
| "Dynamics bridge is assumed" | **CRITICAL** | Axiom | Prove or strengthen |
| "Laplacians are axioms" | Medium | Standard | Define |
| "Energy ≥ 0 is axiom" | Medium | Obvious | Prove |
| "Advection connection unproven" | Medium | "Interpretation" | Prove projection |
| "Pressure unspecified" | Medium | Anticommutator | Derive from div=0 |
| "Tensor product breaks under evolution" | Low-Med | Implicit | Clarify in paper |

---

## Recommended Priority Order

### Immediate (Before Submission):
1. **Fix `IsWeakNSSolution` definition** — Currently vacuous
2. **Fix `IsStrongNSSolution` definition** — Currently vacuous
3. **Prove Laplacian existence** — Convert axioms A1-A2 to definitions

### Short-term (Strengthen Proof):
4. **Prove energy non-negativity** — Axioms B3-B4 → theorems
5. **Prove lift right inverse** — Remove `IntegralCoercionHolds` hypothesis
6. **Prove viscosity formula** — Complete the IBP calculation

### Medium-term (Full Rigor):
7. **Prove advection projection** — [Ψ, D] → (u·∇)u
8. **Prove pressure projection** — {Ψ, D} → ∇p
9. **Clarify evolution structure** — What happens to tensor product form

### Long-term (Ideal State):
10. **Prove dynamics bridge** — Remove axiom D3 entirely
11. **Full Mathlib integration** — Use `MeasureTheory` properly

---

## Axiom Reduction Roadmap

| Phase | Axioms | Reduction |
|-------|--------|-----------|
| Current | 30 | — |
| After A (Laplacians) | 28 | -2 |
| After B (Energy ≥ 0) | 26 | -2 |
| After C (Lift inverse) | 25 | -1 |
| After F (Viscosity) | 24 | -1 |
| After G (Boltzmann bounds) | 22 | -2 |
| **Target** | **~20** | **-10** |

The irreducible core should be ~15-20 axioms encoding:
- Noether/Stone theorems (physics)
- Serrin uniqueness (external NS theory)
- Chapman-Enskog correspondence (kinetic theory)
- The dynamics bridge (if we can't prove it)

---

## Files Needing Modification

| File | Changes |
|------|---------|
| `PhysicsAxioms.lean` | Fix NS solution defs, convert A/B axioms |
| `LiftConstruction.lean` | Remove IntegralCoercionHolds hypothesis |
| `ViscosityEmergence.lean` | Complete IBP proof |
| `DynamicsBridge.lean` | Add advection/pressure projection theorems |
| `BoltzmannPhysics.lean` | Prove pointwise bounds |

---

## Questions for Tracy

1. **NS Solution Definition**: What's the proper Lean formulation of weak NS solutions you want? (Distributional, energy equality, etc.)

2. **Dynamics Bridge**: Is this meant to remain an axiom (physics postulate) or should we attempt to prove it?

3. **Advection Term**: Do you have a worked derivation of how [Ψ, D] → (u·∇)u? This would be key to proving the bridge.

4. **Axiom Target**: What's the acceptable number of physics axioms for the submission? 20? 15? 10?
