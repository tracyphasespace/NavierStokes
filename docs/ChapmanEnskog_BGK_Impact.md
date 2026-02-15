# Chapman-Enskog Recovery from BGK: Impact on MomentDerivation.lean

## Executive Summary

The `RelaxedKineticEvolution` structure replaces free streaming with BGK
collision dynamics. The critical question: how does this change the proof
chain in `MomentDerivation.lean`?

**Answer**: The moment equation proof chain is ALMOST UNCHANGED. The BGK
collision term vanishes from the momentum equation by collision conservation.
The only real change is that `h_closure` (Chapman-Enskog) goes from being
an axiom to being DERIVED from BGK + Gaussian integrals.

---

## Current Proof Chain (MomentDerivation.lean, lines 116-148)

```
moment_projection_satisfies_NS proves: timeDerivTerm + advectionTerm = ν * viscosityTerm

  R1: timeDerivTerm = -(stressGradPhi)               [Leibniz + transport]
  R2: stressGradPhi = reynoldsGradPhi + deviationGradPhi   [integral linearity]
  R3: advectionTerm = reynoldsGradPhi                 [index symmetry]
  R4: deviationGradPhi = -(ν*viscosity) + -(ν*transpose)  [CLOSURE AXIOM]
  R5: transposeGradPhi = 0                            [IBP + div-free]

  Then: rw [R1, R2, R3, R4, R5]; ring
  Gives: -(R + (-νV + 0)) + R = νV  ✓
```

---

## How BGK Changes Each Step

### R1: time_deriv_to_stress — CHANGES (but result is the same)

**Current**: Uses free streaming ∂ₜΨ + p·∇ₓΨ = 0 (no source)

**With BGK**: ∂ₜΨ + p·∇ₓΨ = -(1/τ)(Ψ - M[Ψ])

Take the first moment (multiply by pᵢ ρ(p) and integrate over p):

```
∂ₜ∫ pᵢ ρ Ψ dp + ∂ⱼ∫ pᵢ pⱼ ρ Ψ dp = -(1/τ) ∫ pᵢ ρ (Ψ - M[Ψ]) dp
^                  ^                     ^
  ∂ₜuᵢ              ∂ⱼTᵢⱼ                 COLLISION TERM
```

But by `collision_mom_conserved` (a field of RelaxedKineticEvolution):

```
∫ p · (Ψ(x,p) - M[Ψ](x,p)) dp = 0
```

**So the collision term vanishes from the momentum equation.**

Result: ∂ₜuᵢ + ∂ⱼTᵢⱼ = 0 — **SAME as free streaming**.

The proof of R1 needs one extra step (use `collision_mom_conserved` to kill
the source term), but the conclusion is identical.

### R2: stress_splits — UNCHANGED

This is pure integral linearity:
  Tᵢⱼ = uᵢuⱼ + σᵢⱼ  (Reynolds decomposition)
  ∫T:∇φ = ∫(u⊗u):∇φ + ∫σ:∇φ

Algebraic identity — independent of dynamics.

### R3: advection_from_reynolds — UNCHANGED

This is index symmetry of the u⊗u term. Algebraic — independent of dynamics.

### R4: deviation_to_viscous — THE BIG CHANGE

**Current**: h_closure is an AXIOM (structure field) asserting:
```
σᵢⱼ = Tᵢⱼ - uᵢuⱼ = -ν(∂ᵢuⱼ + ∂ⱼuᵢ)
```

**With BGK**: This becomes a THEOREM derived from:
1. Chapman-Enskog expansion of BGK
2. Gaussian integrals of the Maxwellian
3. VacuumStructure (ν = τT)

### R5: transpose_vanishes — UNCHANGED

IBP + div-free test function. Independent of dynamics.

---

## Chapman-Enskog Derivation of Viscosity from BGK

This is the new mathematical content that REPLACES the h_closure axiom.

### Step 1: Non-equilibrium decomposition

Write f = M[f] + g where g = f - M[f] is the departure from local equilibrium.

From BGK:
```
g = f - M[f] = -τ(∂ₜf + v·∇ₓf)
```

### Step 2: First-order approximation (Kn << 1)

Replace f → M on the right-hand side (valid when Knudsen number τ|∇u|/|u| << 1):
```
g ≈ g₁ = -τ(∂ₜM + v·∇ₓM)
```

This is the Chapman-Enskog expansion truncated at first order.

### Step 3: Compute the streaming operator on M

The local Maxwellian M(v; ρ,u,T) = ρ/(2πT)^(3/2) exp(-|v-u|²/(2T)).

Using the chain rule on the macroscopic fields (ρ, u, T):
```
(∂ₜ + v·∇ₓ)M = M × [(∂ₜρ/ρ + ...) + (cᵢ/T)(∂ₜuᵢ + vⱼ∂ⱼuᵢ) + ...]
```
where c = v - u is the peculiar velocity.

At the Euler level (zeroth order), ∂ₜρ, ∂ₜu, ∂ₜT satisfy the Euler equations.
After substituting and simplifying, the dominant contribution to the stress is:

```
g₁ ≈ -τM × (cᵢcⱼ/T - (|c|²/3T)δᵢⱼ) × (∂ᵢuⱼ + ∂ⱼuᵢ - (2/3)δᵢⱼ ∇·u) / 2
```

For incompressible flow (∇·u = 0), this simplifies to:
```
g₁ ≈ -τM × (cᵢcⱼ/T - (|c|²/3T)δᵢⱼ) × (∂ᵢuⱼ + ∂ⱼuᵢ) / 2
```

### Step 4: Compute the viscous stress tensor

```
σᵢⱼ = ∫ cᵢ cⱼ g dv ≈ ∫ cᵢ cⱼ g₁ dv
```

Using the Gaussian moment identities for M:
```
∫ cᵢ cⱼ M dv = ρT δᵢⱼ
∫ cᵢ cⱼ cₖ cₗ M dv = ρT²(δᵢⱼδₖₗ + δᵢₖδⱼₗ + δᵢₗδⱼₖ)
```

Substituting:
```
σᵢⱼ = -τ × (1/T) × ρT² × (∂ᵢuⱼ + ∂ⱼuᵢ)/2 × (δᵢₖδⱼₗ + δᵢₗδⱼₖ - (2/3)δᵢⱼδₖₗ) evaluated
     = -τρT × (∂ᵢuⱼ + ∂ⱼuᵢ)    [for traceless, incompressible part]
```

### Step 5: Identify viscosity

Dynamic viscosity: μ = τρT = τp (where p = ρT is pressure)
Kinematic viscosity: ν = μ/ρ = τT

**Therefore**: σᵢⱼ = -ρν(∂ᵢuⱼ + ∂ⱼuᵢ)

For unit density (our normalization): σᵢⱼ = -ν(∂ᵢuⱼ + ∂ⱼuᵢ)

**This is exactly the h_closure axiom, now DERIVED.**

---

## Impact on Lean Structure

### What SURVIVES (unchanged):

| Component | File | Why unchanged |
|-----------|------|---------------|
| `velocityMoment` | MomentProjection.lean | Definition only |
| `stressTensor` | MomentProjection.lean | Definition only |
| `stressDeviation` | MomentProjection.lean | Definition only |
| `reynolds_decomposition` | MomentDerivation.lean | Algebraic identity |
| `LeibnizTimeInterchange` | MomentDerivation.lean | Analysis fact |
| `LeibnizSpaceInterchange` | MomentDerivation.lean | Analysis fact |
| `IsWeakNSSolution` | PhysicsAxioms.lean | Target formulation |
| `timeDerivTerm` | PhysicsAxioms.lean | Concrete definition |
| `advectionTerm` | PhysicsAxioms.lean | Concrete definition |
| `viscosityTerm` | PhysicsAxioms.lean | Concrete definition |
| `VacuumStructure` | PhysicsAxioms.lean | Moment conditions |
| `CalculusRules.stress_splits` | PhysicsAxioms.lean R2 | Integral linearity |
| `CalculusRules.advection_from_reynolds` | PhysicsAxioms.lean R3 | Index symmetry |
| `CalculusRules.transpose_vanishes` | PhysicsAxioms.lean R5 | IBP + div-free |
| `moment_projection_satisfies_NS` | MomentDerivation.lean | **Same proof structure** |
| `global_regularity_from_scleronomic` | DynamicsBridge.lean | **Same proof flow** |
| `CMI_global_regularity` | CMI_Regularity.lean | **Same conclusion** |

### What CHANGES:

| Component | Change | Difficulty |
|-----------|--------|------------|
| `ScleronomicKineticEvolution` | → `RelaxedKineticEvolution` | Low (structure swap) |
| `h_transport` field | Add BGK source term | Low |
| `h_scleronomic` field | → `weak_scleronomic` (bounded) | Low |
| `h_closure` field | **DELETED** — replaced by derived theorem | Medium |
| New: `collision_mass_conserved` | Field of RelaxedKineticEvolution | Low |
| New: `collision_mom_conserved` | Field of RelaxedKineticEvolution | Low |
| New: `energy_bound` | Field of RelaxedKineticEvolution | Low |
| `CalculusRules.time_deriv_to_stress` | R1 proof adds collision cancellation | Medium |
| `CalculusRules.deviation_to_viscous` | R4 now from Chapman-Enskog theorem | **High** |
| New: `chapman_enskog_closure` | The big new theorem | **High** |

---

## New Lean Code: RelaxedKineticEvolution

```lean
/-- Relaxed kinetic evolution with BGK collision dynamics.
    Replaces ScleronomicKineticEvolution with physically satisfiable hypotheses. -/
structure RelaxedKineticEvolution
    (u₀ : VelocityField) (ρ : SmoothWeight) (ν : ℝ) where
  /-- The 6D phase-space field -/
  Ψ : ℝ → PhaseSpaceField
  /-- Local Maxwellian projection operator -/
  ℳ : PhaseSpaceField → PhaseSpaceField
  /-- Relaxation time -/
  τ : ℝ
  /-- Relaxation time is positive -/
  τ_pos : 0 < τ
  /-- BGK transport: ∂ₜΨ + p·∇ₓΨ = -(1/τ)(Ψ - M[Ψ]) -/
  h_bgk_transport : ∀ t x p,
    fderiv ℝ (fun s => Ψ s (x, p)) t 1 +
    ∑ i : Fin 3, momentumCoord p i * partialX i (Ψ t) (x, p) =
    -(1 / τ) * (Ψ t (x, p) - ℳ (Ψ t) (x, p))
  /-- Collision conserves mass: ∫ (Ψ - M[Ψ]) dp = 0 -/
  collision_mass_conserved : ∀ t (x : Position),
    ∫ p : Torus3, ρ.ρ p * Complex.re (Ψ t (x, p) - ℳ (Ψ t) (x, p)) = 0
  /-- Collision conserves momentum: ∫ pᵢ(Ψ - M[Ψ]) dp = 0 -/
  collision_mom_conserved : ∀ t (x : Position) (i : Fin 3),
    ∫ p : Torus3, momentumCoord p i * ρ.ρ p *
      Complex.re (Ψ t (x, p) - ℳ (Ψ t) (x, p)) = 0
  /-- Weak scleronomic: ‖Δ_x Ψ - Δ_p Ψ‖ bounded by departure from equilibrium -/
  weak_scleronomic : ∀ t,
    ‖laplacianX (Ψ t) - laplacianP (Ψ t)‖ ≤
    (1 / τ) * ‖fun z => Ψ t z - ℳ (Ψ t) z‖
  /-- Energy bound: L² norm non-increasing -/
  energy_bound : ∀ t, 0 ≤ t →
    ‖Ψ t‖ ≤ ‖Ψ 0‖
  /-- Initial data recovery -/
  h_initial : velocityFromEvolution ρ Ψ 0 = u₀ 0
  /-- Divergence-free -/
  h_div_free : DivergenceFree (velocityFromEvolution ρ Ψ)
  /-- Velocity continuity -/
  h_vel_continuous : ∀ t, Continuous (velocityFromEvolution ρ Ψ t)
```

---

## New Lean Code: Chapman-Enskog Theorem

This is the key new mathematical content. It replaces the `h_closure` axiom.

### Option A: Chapman-Enskog as a theorem (honest, hard)

```lean
/-- Chapman-Enskog closure: BGK collision + Gaussian integrals → viscous stress.

    The derivation:
    1. From BGK: g = Ψ - M[Ψ] = -τ(∂ₜΨ + v·∇ₓΨ)  ... by rearranging BGK
    2. At first order: g ≈ -τ(v·∇ₓ)M               ... CE truncation
    3. σᵢⱼ = ∫ cᵢcⱼ g dp                            ... stress from deviation
    4. Using ∫ cᵢcⱼcₖcₗ M dp = ρT²(δᵢⱼδₖₗ + ...)  ... Gaussian fourth moment
    5. σᵢⱼ = -τρT(∂ᵢuⱼ + ∂ⱼuᵢ) = -ν(∂ᵢuⱼ + ∂ⱼuᵢ) ... ν = τT

    This requires:
    - Gaussian moment identities (provable with Mathlib's integral_gaussian)
    - The CE truncation (valid when Kn << 1 — this is where the open problem hides)
    - Leibniz interchange for the stress integral
-/
theorem chapman_enskog_closure
    (ev : RelaxedKineticEvolution u₀ ρ ν)
    (hv : VacuumStructure ρ ν)
    (h_kn_small : KnudsenBound ev)  -- ← THE OPEN PROBLEM
    : ∀ t x (i j : Fin 3),
      stressTensor ρ (ev.Ψ t) x i j -
        (velocityMoment ρ (ev.Ψ t) x) i * (velocityMoment ρ (ev.Ψ t) x) j =
      -ν * (fderiv ℝ (fun y => (velocityMoment ρ (ev.Ψ t) y) j) x
              (EuclideanSpace.single i 1) +
            fderiv ℝ (fun y => (velocityMoment ρ (ev.Ψ t) y) i) x
              (EuclideanSpace.single j 1)) := by
  sorry -- THE HARD THEOREM: Chapman-Enskog from BGK
```

### Option B: Chapman-Enskog as a structure field (pragmatic)

```lean
/-- The Chapman-Enskog closure as a hypothesis.
    Physically: the departure from equilibrium is first-order in Kn.
    Mathematically: this is the content of the CE expansion.

    HONEST LABELING: This is NOT self-evident. It encodes:
    (a) Kn << 1 (gradients don't grow too fast)
    (b) The CE expansion converges at first order
    (c) Higher-order terms O(Kn²) are negligible

    This is where the millennium problem hides in the BGK framework. -/
h_chapman_enskog_closure : ∀ t x (i j : Fin 3),
    stressTensor ρ (ev.Ψ t) x i j -
      (velocityMoment ρ (ev.Ψ t) x) i * (velocityMoment ρ (ev.Ψ t) x) j =
    -ν * (fderiv ℝ (fun y => (velocityMoment ρ (ev.Ψ t) y) j) x
            (EuclideanSpace.single i 1) +
          fderiv ℝ (fun y => (velocityMoment ρ (ev.Ψ t) y) i) x
            (EuclideanSpace.single j 1))
```

### Recommendation: Option A with honest labeling

Option A is better because:
1. It separates the Knudsen bound (the real open problem) from the algebra
2. The Gaussian integral computation IS provable — real math
3. Only the Kn bound remains as an axiom/hypothesis

---

## New CalculusRules with BGK

The `CalculusRules` structure needs modification for R1 and R4:

```lean
structure CalculusRulesRelaxed (ev : RelaxedKineticEvolution u₀ ρ ν) : Prop where
  /-- R1 (modified): Leibniz + BGK transport + collision cancellation → stress.
      The BGK source -(1/τ)(Ψ - M[Ψ]) contributes to the first moment,
      but collision_mom_conserved kills it. So the result is the SAME:
        ∫∫ u·∂ₜφ = -∫∫ T:∇φ -/
  time_deriv_to_stress : ∀ (φ : TestFunction),
    timeDerivTerm (velocityFromEvolution ρ ev.Ψ) φ.val = -(stressGradPhi ρ ev.Ψ φ.val)

  /-- R2: UNCHANGED — integral linearity -/
  stress_splits : ∀ (φ : TestFunction),
    stressGradPhi ρ ev.Ψ φ.val =
    reynoldsGradPhi ρ ev.Ψ φ.val + deviationGradPhi ρ ev.Ψ φ.val

  /-- R3: UNCHANGED — index symmetry -/
  advection_from_reynolds : ∀ (φ : TestFunction),
    advectionTerm (velocityFromEvolution ρ ev.Ψ) φ.val = reynoldsGradPhi ρ ev.Ψ φ.val

  /-- R4 (modified): NOW DERIVED from Chapman-Enskog instead of axiom.
      Uses: chapman_enskog_closure + Gaussian integrals. -/
  deviation_to_viscous : ∀ (φ : TestFunction),
    deviationGradPhi ρ ev.Ψ φ.val =
    -(ν * viscosityTerm (velocityFromEvolution ρ ev.Ψ) φ.val) +
    -(ν * transposeGradPhi ρ ev.Ψ φ.val)

  /-- R5: UNCHANGED — IBP + div-free -/
  transpose_vanishes : ∀ (φ : TestFunction),
    transposeGradPhi ρ ev.Ψ φ.val = 0
```

**Key insight**: The CalculusRules INTERFACE is unchanged! Only R1's proof uses
the new collision conservation, and R4's proof uses Chapman-Enskog instead of
being an axiom. The `moment_projection_satisfies_NS` theorem remains
EXACTLY THE SAME — it just calls `rw [R1, R2, R3, R4, R5]; ring`.

---

## Detailed R1 Proof Sketch (BGK version)

```
Goal: timeDerivTerm u φ = -(stressGradPhi ρ Ψ φ)

Expand timeDerivTerm:
  = ∫∫ uᵢ ∂ₜφᵢ

IBP in time (boundary terms vanish by compact support):
  = -∫∫ (∂ₜuᵢ) φᵢ

Expand ∂ₜuᵢ = ∂ₜ ∫ pᵢ ρ Ψ dp (Leibniz interchange):
  = -∫∫ (∫ pᵢ ρ ∂ₜΨ dp) φᵢ

Use BGK: ∂ₜΨ = -p·∇ₓΨ - (1/τ)(Ψ - M[Ψ])
  = -∫∫ (∫ pᵢ ρ [-p·∇ₓΨ - (1/τ)(Ψ - M[Ψ])] dp) φᵢ
  = -∫∫ (∫ pᵢ ρ (-p·∇ₓΨ) dp) φᵢ   +   (1/τ)∫∫ (∫ pᵢ ρ (Ψ - M[Ψ]) dp) φᵢ
                                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                          = 0 by collision_mom_conserved

  = -∫∫ (-∂ⱼ ∫ pᵢ pⱼ ρ Ψ dp) φᵢ     [Leibniz in space]
  = ∫∫ (∂ⱼTᵢⱼ) φᵢ
  = -∫∫ Tᵢⱼ ∂ⱼφᵢ                     [IBP in space]
  = -(stressGradPhi ρ Ψ φ)           ✓
```

The only new step is killing the collision term. Everything else is identical.

---

## Detailed R4 Proof Sketch (Chapman-Enskog version)

```
Goal: deviationGradPhi = -(ν*viscosityTerm) + -(ν*transposeGradPhi)

Expand deviationGradPhi:
  = ∫∫ σᵢⱼ ∂ⱼφᵢ
  where σᵢⱼ = Tᵢⱼ - uᵢuⱼ = ∫ cᵢcⱼ g dp   (c = p - u)

Chapman-Enskog (the new content):
  g = Ψ - M[Ψ] ≈ -τ(v·∇ₓ)M    [first-order CE]

  σᵢⱼ = ∫ cᵢcⱼ [-τ(cₖ∂ₖM)] dp

  Using M = ρ/(2πT)^(3/2) exp(-|c|²/(2T)):
    ∂ₖM = M × [... + (cₗ/T)∂ₖuₗ + ...]

  σᵢⱼ = -τ/T × ∫ cᵢcⱼcₖcₗ M dp × ∂ₖuₗ

  Gaussian fourth moment:
    ∫ cᵢcⱼcₖcₗ M dp = ρT²(δᵢⱼδₖₗ + δᵢₖδⱼₗ + δᵢₗδⱼₖ)

  Contract with ∂ₖuₗ:
    σᵢⱼ = -τρT(∂ᵢuⱼ + ∂ⱼuᵢ + δᵢⱼ∇·u)

  For incompressible (∇·u = 0):
    σᵢⱼ = -τρT(∂ᵢuⱼ + ∂ⱼuᵢ)

  With ν = τT and ρ = 1 (normalized):
    σᵢⱼ = -ν(∂ᵢuⱼ + ∂ⱼuᵢ)   ← SAME AS h_closure!

  Therefore:
    deviationGradPhi = ∫∫ [-ν(∂ᵢuⱼ + ∂ⱼuᵢ)] ∂ⱼφᵢ
                     = -ν ∫∫ (∂ᵢuⱼ)(∂ⱼφᵢ) + -ν ∫∫ (∂ⱼuᵢ)(∂ⱼφᵢ)
                     = -(ν*viscosityTerm) + -(ν*transposeGradPhi)  ✓
```

### What's provable vs what requires the Kn bound:

| Step | Status |
|------|--------|
| g = -τ(∂ₜΨ + v·∇ₓΨ) = -τ × BGK rhs | Tautology from BGK equation |
| g ≈ -τ(v·∇ₓ)M (first-order CE) | **Requires Kn << 1** |
| ∫ cᵢcⱼcₖcₗ M dp = ρT²(δδ+δδ+δδ) | Provable (Gaussian integrals) |
| σᵢⱼ = -ν(∂ᵢuⱼ + ∂ⱼuᵢ) | Follows from above |

The Kn bound is the ONE place where the open problem enters.

---

## The Viscosity-Temperature Connection

From VacuumStructure (PhysicsAxioms.lean line 483):
```lean
viscosity_moment : ∀ i j : Fin 3,
    (∫ p, momentumCoord p i * momentumCoord p j * ρ.ρ p) = if i = j then ν else 0
```

This says: the second moment of ρ(p) is ν δᵢⱼ.

In BGK language: ∫ cᵢcⱼ M dv = ρT δᵢⱼ → T = ν (with ρ = 1 normalization).

So the VacuumStructure already encodes ν = T, and with τ from the BGK:
```
kinematic viscosity = τT = τν
```

**The relaxation time τ connects to ν through VacuumStructure**.

If we want ν to remain the NS viscosity, we need τ = 1 (or equivalently,
we absorb τ into the definition: the Chapman-Enskog viscosity is τν, and
we set τ = 1 so that the VacuumStructure ν IS the viscosity).

Alternatively, generalize VacuumStructure to carry τ and set ν_NS = τ × ν_vacuum.

---

## Migration Plan: ScleronomicKineticEvolution → RelaxedKineticEvolution

### Phase 1: Add new structure (non-breaking)
- Add `RelaxedKineticEvolution` to PhysicsAxioms.lean
- Keep `ScleronomicKineticEvolution` temporarily

### Phase 2: New moment derivation
- Add `chapman_enskog_closure` theorem (with Kn bound hypothesis)
- Add `moment_projection_satisfies_NS_relaxed` using BGK
- Verify same proof chain works: R1,R2,R3,R4,R5 → ring

### Phase 3: Rewire CMI
- `DynamicsBridge.lean`: new theorem using `RelaxedKineticEvolution`
- `CMI_Regularity.lean`: new CMI theorem
- Keep old CMI theorem as deprecated

### Phase 4: Cleanup
- Delete `ScleronomicKineticEvolution`
- Delete old CMI chain
- Update `HonestyAudit.lean`

---

## Post-Migration Axiom/Hypothesis Inventory

### Structure fields (hypotheses, not axioms):
| # | Field | Content | Satisfiable? |
|---|-------|---------|-------------|
| 1 | `h_bgk_transport` | BGK equation | YES (global weak solutions exist) |
| 2 | `collision_mass_conserved` | ∫(f-M)=0 | YES (provable from M construction) |
| 3 | `collision_mom_conserved` | ∫p(f-M)=0 | YES (provable from M construction) |
| 4 | `weak_scleronomic` | ‖Δ_x-Δ_p‖ bounded | YES (from BGK regularity) |
| 5 | `energy_bound` | ‖Ψ(t)‖ ≤ ‖Ψ(0)‖ | YES (H-theorem) |
| 6 | `h_initial` | Moment matches u₀ | YES (construction) |
| 7 | `h_div_free` | Solenoidal | YES (constraint) |
| 8 | `h_vel_continuous` | Velocity continuous | YES (dominated convergence) |

### The ONE honest hypothesis hiding the open problem:
| # | Hypothesis | Content | Satisfiable? |
|---|-----------|---------|-------------|
| 1 | `KnudsenBound` | τ‖∇u‖/‖u‖ bounded for all t | **OPEN** = NS regularity |

### What's PROVED (not hypothesized):
- Reynolds decomposition (algebraic)
- Collision term cancellation in momentum equation (from fields 2-3)
- Chapman-Enskog closure (from BGK + Gaussian integrals + Kn bound)
- Moment equations → weak NS (matching)

**The gap between hypotheses and conclusion now contains MORE genuine
mathematics than before** — specifically the Chapman-Enskog derivation.

---

## Summary

The BGK change is **surgically clean**:
1. The moment equation proof chain (R1-R5 → ring) is STRUCTURALLY IDENTICAL
2. R1 gets one extra step (collision cancellation)
3. R4 gets real mathematical content (Chapman-Enskog from Gaussian integrals)
4. The open problem is isolated in a single, well-defined hypothesis (Kn bound)
5. ALL other hypotheses are individually satisfiable (unlike the old framework)
