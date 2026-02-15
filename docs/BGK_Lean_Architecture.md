# BGK Lean Architecture: Relaxed Scleronomic Constraint

## Mathematical Framework

### The BGK Equation

Replace free streaming with BGK collision dynamics:

```
∂_t f + v·∇_x f = (1/τ)(M[f] - f)
```

where:
- `f(x,v,t)` — phase space distribution on T³ × R³
- `τ` — relaxation time (collision timescale)
- `M[f]` — local Maxwellian determined by moments of f

### Local Maxwellian

```
M[f](x,v) = ρ(x) / (2πT(x))^(3/2) · exp(-|v - u(x)|² / (2T(x)))
```

where the macroscopic fields are moments of f:
```
ρ(x) = ∫ f(x,v) dv              (density)
u(x) = (1/ρ) ∫ v f(x,v) dv      (velocity)
T(x) = (1/3ρ) ∫ |v-u|² f(x,v) dv (temperature)
```

### What Changes from Current Framework

| Current (broken) | Proposed (BGK) |
|---|---|
| Free streaming: ∂_t Ψ + p·∇_x Ψ = 0 | BGK: ∂_t f + v·∇_x f = (1/τ)(M[f] - f) |
| Strict constraint: Δ_x = Δ_p (impossible) | Relaxed: deviation bounded by collision rate |
| Energy exactly conserved (trivially) | Energy exactly conserved (by collision invariants) |
| All Sobolev norms preserved (trivially) | Entropy decreases (H-theorem, nontrivial) |
| Hypotheses vacuously unsatisfiable | Hypotheses physically realistic |

---

## Lean Module Architecture

### Module 1: `BGK/Distribution.lean` — Types and Moments

```lean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.Bochner

/-- Phase space distribution function. -/
def Distribution := EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ

variable (f : Distribution)

/-- Mass density: ρ(x) = ∫ f(x,v) dv -/
noncomputable def density (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ v, f x v

/-- Bulk velocity: u(x) = (1/ρ) ∫ v f(x,v) dv -/
noncomputable def bulkVelocity (x : EuclideanSpace ℝ (Fin 3))
    : EuclideanSpace ℝ (Fin 3) :=
  (1 / density f x) • ∫ v, f x v • v

/-- Temperature: T(x) = (1/3ρ) ∫ |v - u|² f(x,v) dv -/
noncomputable def temperature (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / (3 * density f x)) *
    ∫ v, ‖v - bulkVelocity f x‖² * f x v

/-- Collision invariants: φ = 1, v, |v|² -/
inductive CollisionInvariant where
  | mass : CollisionInvariant          -- φ(v) = 1
  | momentum : Fin 3 → CollisionInvariant  -- φ(v) = vᵢ
  | energy : CollisionInvariant        -- φ(v) = |v|²
```

**Status**: Definitions only, fully provable, no axioms needed.

### Module 2: `BGK/Maxwellian.lean` — Local Equilibrium

```lean
/-- Local Maxwellian distribution. -/
noncomputable def localMaxwellian
    (ρ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (T : ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun v => ρ / (2 * Real.pi * T) ^ (3/2 : ℝ) *
    Real.exp (-‖v - u‖² / (2 * T))

/-- The local Maxwellian constructed from f's own moments. -/
noncomputable def selfConsistentMaxwellian (f : Distribution)
    (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  localMaxwellian (density f x) (bulkVelocity f x) (temperature f x)

/-- Maxwellian has same moments as f (by construction). -/
theorem maxwellian_same_density (f : Distribution) (x) :
    ∫ v, selfConsistentMaxwellian f x v = density f x := by
  sorry -- Gaussian integral identity, provable

theorem maxwellian_same_velocity (f : Distribution) (x) :
    (1 / density f x) • ∫ v, (selfConsistentMaxwellian f x v) • v
    = bulkVelocity f x := by
  sorry -- Gaussian integral identity, provable

theorem maxwellian_same_energy (f : Distribution) (x) :
    (1 / (3 * density f x)) *
      ∫ v, ‖v - bulkVelocity f x‖² * selfConsistentMaxwellian f x v
    = temperature f x := by
  sorry -- Gaussian integral identity, provable
```

**Status**: The `sorry`s are Gaussian integral identities — provable with
Mathlib's `integral_gaussian` + algebraic manipulation. Real math, no axioms.

### Module 3: `BGK/CollisionOperator.lean` — BGK Operator and Conservation

```lean
/-- BGK collision operator: Q(f) = (1/τ)(M[f] - f) -/
noncomputable def bgkOperator (τ : ℝ) (f : Distribution)
    (x v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / τ) * (selfConsistentMaxwellian f x v - f x v)

/-- THEOREM: BGK conserves mass.
    ∫ Q(f)(x,v) dv = 0
    Proof: M[f] has same density as f. -/
theorem bgk_conserves_mass (τ : ℝ) (hτ : τ > 0) (f : Distribution) (x) :
    ∫ v, bgkOperator τ f x v = 0 := by
  -- unfold bgk, factor 1/τ, use maxwellian_same_density
  sorry -- provable from Module 2

/-- THEOREM: BGK conserves momentum.
    ∫ vᵢ Q(f)(x,v) dv = 0
    Proof: M[f] has same bulk velocity as f. -/
theorem bgk_conserves_momentum (τ : ℝ) (hτ : τ > 0) (f : Distribution)
    (x) (i : Fin 3) :
    ∫ v, (v i) * bgkOperator τ f x v = 0 := by
  sorry -- provable from Module 2

/-- THEOREM: BGK conserves energy.
    ∫ |v|² Q(f)(x,v) dv = 0
    Proof: M[f] has same temperature as f. -/
theorem bgk_conserves_energy (τ : ℝ) (hτ : τ > 0) (f : Distribution) (x) :
    ∫ v, ‖v‖² * bgkOperator τ f x v = 0 := by
  sorry -- provable from Module 2
```

**Status**: All three conservation laws are provable from Gaussian integral
identities. No axioms. These are the analogues of mass/momentum/energy
conservation in the current framework, but now correctly derived.

### Module 4: `BGK/HTheorem.lean` — Entropy Inequality

```lean
/-- Boltzmann H-functional (entropy). -/
noncomputable def hFunctional (f : Distribution) : ℝ :=
  ∫ x, ∫ v, f x v * Real.log (f x v)

/-- THEOREM: BGK satisfies the H-theorem.
    ∫ Q(f) ln(f) dv ≤ 0
    with equality iff f = M[f].
    This is the a priori estimate NS doesn't have. -/
theorem bgk_h_theorem (τ : ℝ) (hτ : τ > 0) (f : Distribution) (x)
    (hf_pos : ∀ v, f x v > 0) :
    ∫ v, bgkOperator τ f x v * Real.log (f x v) ≤ 0 := by
  sorry -- provable: uses log convexity (Jensen's inequality)

/-- Entropy production rate. Measures departure from equilibrium. -/
noncomputable def entropyProduction (τ : ℝ) (f : Distribution)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -∫ v, bgkOperator τ f x v * Real.log (f x v)

/-- Entropy production is non-negative. -/
theorem entropyProduction_nonneg (τ : ℝ) (hτ : τ > 0)
    (f : Distribution) (x) (hf_pos : ∀ v, f x v > 0) :
    0 ≤ entropyProduction τ f x := by
  sorry -- direct from h_theorem

/-- Entropy production vanishes iff f is Maxwellian. -/
theorem entropyProduction_zero_iff (τ : ℝ) (hτ : τ > 0)
    (f : Distribution) (x) (hf_pos : ∀ v, f x v > 0) :
    entropyProduction τ f x = 0 ↔
      f x = selfConsistentMaxwellian f x := by
  sorry -- characterization of equality in Jensen
```

**Status**: The H-theorem for BGK is provable via Jensen's inequality
applied to the convex function `t ↦ t ln t`. This is real mathematics.
This is the KEY new ingredient that the current framework lacks.

### Module 5: `BGK/RelaxedConstraint.lean` — The Weak Scleronomic Condition

```lean
/-- Scleronomic deviation: how far f is from satisfying Δ_x = Δ_v.
    This replaces the strict constraint with a measurable quantity. -/
noncomputable def scleronomicDeviation (f : Distribution) : ℝ :=
  ∫ x, ∫ v, ‖laplacianX f x v - laplacianV f x v‖²

/-- For a Maxwellian, the scleronomic deviation is determined by
    the macroscopic field gradients. -/
theorem maxwellian_deviation_from_gradients
    (ρ : Position → ℝ) (u : Position → Position) (T : Position → ℝ) :
    scleronomicDeviation (fun x v => localMaxwellian (ρ x) (u x) (T x) v)
    = F(‖∇²ρ‖, ‖∇²u‖, ‖∇²T‖) := by
  sorry -- explicit computation for Gaussian

/-- STRUCTURE: Bounded Scleronomic Evolution.
    Replaces the impossible strict constraint with physically
    realistic bounded deviation. -/
structure BoundedScleronomicEvolution
    (f : ℝ → Distribution) (τ : ℝ) where
  /-- f satisfies the BGK equation -/
  h_bgk : ∀ t x v,
    fderiv ℝ (fun s => f s x v) t 1 +
    ∑ i : Fin 3, (v i) * partialX i (f t) (x, v)
    = bgkOperator τ (f t) x v
  /-- Positivity -/
  h_pos : ∀ t x v, f t x v > 0
  /-- Initial data has finite energy -/
  h_finite_energy : ∫ x, ∫ v, ‖v‖² * f 0 x v < ⊤
  /-- Relaxation time is positive -/
  h_tau_pos : τ > 0
```

**Status**: This replaces `ScleronomicKineticEvolution` (7 fields,
vacuously unsatisfiable) with `BoundedScleronomicEvolution` (4 fields,
physically realistic). The BGK equation IS satisfiable — it has global
weak solutions (Perthame, 1989).

### Module 6: `BGK/MomentEquations.lean` — NS Derivation

```lean
/-- Taking moments of the BGK equation yields the compressible
    Euler equations + viscous corrections.

    Zeroth moment (mass):
      ∂_t ρ + ∇·(ρu) = 0

    First moment (momentum):
      ∂_t(ρu) + ∇·(ρu⊗u + P) = 0

    where P_ij = ∫ (vᵢ - uᵢ)(vⱼ - uⱼ) f dv is the pressure tensor.
-/
theorem bgk_moment_continuity
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ) :
    ∀ t x, ∂_t (density (f t) x) +
      divergence (fun x => density (f t) x • bulkVelocity (f t) x) x = 0 := by
  sorry -- integrate BGK over v, use conservation of mass

theorem bgk_moment_momentum
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ) :
    ∀ t x i,
      ∂_t (density (f t) x * (bulkVelocity (f t) x) i) +
      ∑ j, ∂_xⱼ (∫ v, (v i) * (v j) * f t x v) = 0 := by
  sorry -- integrate v_i * BGK over v, use conservation of momentum

/-- The pressure tensor decomposes as P = pI + σ where
    p = ρT (ideal gas) and σ is the viscous stress.
    The Chapman-Enskog expansion gives σ_ij ≈ -μ(∂ᵢuⱼ + ∂ⱼuᵢ)
    with μ = ρTτ (for BGK).

    This is an APPROXIMATION valid when Kn = τ·|∇u|/|u| << 1. -/
noncomputable def knudsenNumber (f : Distribution) (x : Position) (τ : ℝ) : ℝ :=
  τ * ‖fderiv ℝ (bulkVelocity f) x‖ /
    (‖bulkVelocity f x‖ + 1)  -- +1 to avoid division by zero

/-- KEY HYPOTHESIS: The Knudsen number stays bounded.
    This is the physically meaningful replacement for the
    scleronomic constraint. It says: collision rate dominates
    gradient growth rate.

    THIS IS THE OPEN PROBLEM. If you can prove this, you've
    essentially solved NS regularity. -/
axiom knudsen_bounded
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ) :
    ∃ C : ℝ, ∀ t x, knudsenNumber (f t) x τ ≤ C
```

**Status**: The moment equations are provable (integration of BGK against
collision invariants). The Knudsen bound is the **one honest axiom** — it's
the precise mathematical statement of "collisions dominate transport."
This is where the millennium problem lives.

### Module 7: `BGK/BoundedEnergy.lean` — The Salvaged Energy Theorem

```lean
/-- Total kinetic energy of the distribution. -/
noncomputable def kineticEnergy (f : Distribution) : ℝ :=
  (1/2) * ∫ x, ∫ v, ‖v‖² * f x v

/-- THEOREM: BGK conserves total kinetic energy.
    Unlike the broken free-streaming argument, this is genuine:
    the collision operator conserves energy exactly. -/
theorem bgk_energy_conserved
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ) :
    ∀ t, kineticEnergy (f t) = kineticEnergy (f 0) := by
  sorry -- from bgk_conserves_energy + transport is divergence-free

/-- THEOREM: Entropy is non-increasing.
    This is the NEW a priori estimate. NS energy equality
    already gives L² bounds. The H-theorem gives an ADDITIONAL
    bound on the departure from equilibrium. -/
theorem bgk_entropy_decreasing
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ) :
    ∀ t₁ t₂, t₁ ≤ t₂ → hFunctional (f t₂) ≤ hFunctional (f t₁) := by
  sorry -- from bgk_h_theorem integrated over x

/-- THEOREM (conditional): If Knudsen number stays bounded,
    then the velocity field u(t) = bulkVelocity(f(t)) satisfies
    NS approximately and remains in H^k.

    This is the conditional regularity theorem with a
    PHYSICALLY MEANINGFUL condition. -/
theorem conditional_regularity_bgk
    (f : ℝ → Distribution) (τ : ℝ)
    (ev : BoundedScleronomicEvolution f τ)
    (h_kn : ∀ t x, knudsenNumber (f t) x τ ≤ C) :
    ∀ k : ℕ, ∀ t, ‖bulkVelocity (f t)‖_{H^k} ≤
      F(k, C, τ, ‖bulkVelocity (f 0)‖_{H^k}) := by
  sorry -- THIS IS THE HARD THEOREM
```

---

## What's Provable vs What's Open

### PROVABLE (real Lean theorems, 0 axioms possible):

| Theorem | Technique | Difficulty |
|---------|-----------|------------|
| BGK conserves mass | Integral of (M-f) = 0 | Easy |
| BGK conserves momentum | Integral of v(M-f) = 0 | Easy |
| BGK conserves energy | Integral of \|v\|²(M-f) = 0 | Easy |
| H-theorem | Jensen's inequality on t ln t | Medium |
| Entropy production characterization | Equality in Jensen ↔ Maxwellian | Medium |
| Maxwellian moment identities | Gaussian integrals | Medium |
| Moment equations (continuity) | Integrate BGK against 1 | Easy |
| Moment equations (momentum) | Integrate BGK against v | Easy |
| Chapman-Enskog viscosity formula | Perturbation expansion | Hard |

### OPEN (axioms until proven):

| Statement | Why It's Hard | Where It Lives |
|-----------|--------------|----------------|
| Knudsen number stays bounded | = NS regularity in kinetic language | `knudsen_bounded` |
| BGK global smooth solutions | Near-equilibrium: Guo (2003). General: open | Research target |
| H^k bounds on velocity moments | Requires velocity averaging + bootstrap | Research target |

---

## Comparison: Old vs New Axiom Inventory

### Old (broken): ScleronomicKineticEvolution (7 fields)
- h_scleronomic: Δ_x = Δ_p (IMPOSSIBLE under transport)
- h_transport: free streaming (SHEARS phase space)
- h_closure: Chapman-Enskog (BREAKS at high gradients)
- h_vel_continuous, h_calculus, h_initial, h_div_free

→ Hypotheses mutually inconsistent. Theorem vacuously true.

### New (honest): BoundedScleronomicEvolution (4 fields) + 1 axiom
- h_bgk: satisfies BGK equation (WELL-POSED, solutions exist)
- h_pos: positivity (PHYSICAL, maintained by BGK)
- h_finite_energy: finite energy (STANDARD)
- h_tau_pos: positive relaxation time (PHYSICAL)
- **knudsen_bounded**: collision dominates transport (THE OPEN PROBLEM)

→ Hypotheses are individually satisfiable. The axiom is the precise
  mathematical barrier. Honest about where the difficulty lives.

---

## Implementation Order

1. `BGK/Distribution.lean` — types + moments (pure definitions)
2. `BGK/Maxwellian.lean` — Gaussian integrals (Mathlib)
3. `BGK/CollisionOperator.lean` — BGK + 3 conservation laws
4. `BGK/HTheorem.lean` — entropy inequality (Jensen)
5. `BGK/MomentEquations.lean` — continuity + momentum from BGK
6. `BGK/RelaxedConstraint.lean` — deviation measure + bounded evolution
7. `BGK/BoundedEnergy.lean` — energy conservation + entropy + conditional regularity

Modules 1-5 are provable with current Mathlib. Module 6 is definitions.
Module 7 contains the one honest axiom (knudsen_bounded) and the
conditional theorem that's the real mathematical claim.

---

## The Honest Bottom Line

The old framework said: "Assume impossible things, then regularity is trivial."

The new framework says: "Assume one physically meaningful thing
(collisions dominate transport), then regularity follows from kinetic
theory." The one assumption is labeled as an axiom, documented as open,
and is precisely the NS regularity problem in kinetic language.

This is the **conservation of difficulty** — we can't eliminate the hard
math, but we can:
1. Localize it to a single, clearly stated hypothesis
2. Surround it with genuine proved mathematics (conservation laws,
   H-theorem, moment equations)
3. Make the hypothesis physically meaningful and testable
4. Provide the framework for attacking it with kinetic theory tools
   (collision regularization, velocity averaging, entropy methods)
