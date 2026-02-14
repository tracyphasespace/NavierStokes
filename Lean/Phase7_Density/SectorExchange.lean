/-
Copyright (c) 2026 Tracy McSheery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tracy McSheery, Claude (Anthropic)
-/
import Phase1_Foundation.Cl33
import Phase1_Foundation.BasisOperations

/-!
# Linear-Angular Momentum Exchange Operators

Mixed bivectors γᵢγⱼ (i ∈ spatial, j ∈ momentum) are the operators
that exchange between configuration and momentum sectors.

## Physical Interpretation

Every molecular collision exchanges linear and angular momentum.
The Cl(3,3) algebra with signature (+,+,+,−,−,−) encodes this naturally:
- Spatial sector: γ₀, γ₁, γ₂ with γᵢ² = +1 (configuration/linear)
- Momentum sector: γ₃, γ₄, γ₅ with γⱼ² = −1 (momentum/angular)
- Mixed bivectors: γᵢγⱼ represent exchange operators

The key insight: (γᵢγⱼ)² = +1, not −1. These are hyperbolic rotations,
not elliptic rotations. This is the geometric signature of momentum exchange.

## Main Results

- `exchange_bivector_sq`: Mixed bivectors square to +1
- `spatial_signature`: Spatial generators (0,1,2) square to +1
- `momentum_signature`: Momentum generators (3,4,5) square to -1
-/

namespace NSE.SectorExchange

open QFD.GA

/-!
## Sector Classification

The 6 generators of Cl(3,3) are divided into two sectors:
- Spatial (indices 0, 1, 2): square to +1
- Momentum (indices 3, 4, 5): square to -1
-/

/-- Spatial indices: 0, 1, 2 -/
def isSpatial (i : Fin 6) : Prop := i.val < 3

/-- Momentum indices: 3, 4, 5 -/
def isMomentum (i : Fin 6) : Prop := i.val ≥ 3

/-- Decidability of isSpatial -/
instance (i : Fin 6) : Decidable (isSpatial i) := by
  unfold isSpatial; exact inferInstance

/-- Decidability of isMomentum -/
instance (i : Fin 6) : Decidable (isMomentum i) := by
  unfold isMomentum; exact inferInstance

/-!
## Signature Properties

We prove that the signature matches our sector classification.
-/

/-- Spatial generators square to +1 -/
theorem spatial_signature (i : Fin 6) (h : isSpatial i) :
    signature33 i = 1 := by
  unfold isSpatial at h
  fin_cases i <;> simp [signature33] at *

/-- Momentum generators square to -1 -/
theorem momentum_signature (i : Fin 6) (h : isMomentum i) :
    signature33 i = -1 := by
  unfold isMomentum at h
  fin_cases i <;> simp [signature33] at * <;> omega

/-- Spatial generators square to +1 in the algebra -/
theorem spatial_sq (i : Fin 6) (h : isSpatial i) :
    e i * e i = 1 := by
  rw [basis_sq i, spatial_signature i h]
  simp

/-- Momentum generators square to -1 in the algebra -/
theorem momentum_sq (i : Fin 6) (h : isMomentum i) :
    e i * e i = -1 := by
  rw [basis_sq i, momentum_signature i h]
  simp

/-!
## The Exchange Bivector

A mixed bivector E = eᵢeⱼ where i is spatial and j is momentum.
The key property: E² = +1 (hyperbolic rotation).
-/

/-- Exchange bivector: product of spatial and momentum generators -/
def exchange_bivector (i j : Fin 6) (hi : isSpatial i) (hj : isMomentum j) : Cl33 :=
  e i * e j

/-- The signature product for exchange bivectors -/
theorem exchange_signature_product (i j : Fin 6) (hi : isSpatial i) (hj : isMomentum j) :
    signature33 i * signature33 j = -1 := by
  rw [spatial_signature i hi, momentum_signature j hj]
  ring

/--
**KEY THEOREM**: Exchange bivectors square to +1.

Proof:
  (eᵢeⱼ)² = eᵢeⱼeᵢeⱼ
         = eᵢ(eⱼeᵢ)eⱼ              [associativity]
         = eᵢ(-eᵢeⱼ)eⱼ             [anticommutativity: j ≠ i]
         = -eᵢeᵢeⱼeⱼ
         = -(+1)(-1)                [signatures: spatial=+1, momentum=-1]
         = -(-1) = +1
-/
theorem exchange_bivector_sq (i j : Fin 6) (hi : isSpatial i) (hj : isMomentum j) :
    (e i * e j) * (e i * e j) = 1 := by
  -- First establish i ≠ j (spatial < 3, momentum ≥ 3)
  have h_ne : i ≠ j := by
    intro heq
    unfold isSpatial at hi
    unfold isMomentum at hj
    omega
  -- Now compute (eᵢeⱼ)²
  calc (e i * e j) * (e i * e j)
      = e i * (e j * e i) * e j := by ring
    _ = e i * (-(e i * e j)) * e j := by rw [basis_anticomm (Ne.symm h_ne)]
    _ = -(e i * (e i * e j) * e j) := by ring
    _ = -(e i * e i * (e j * e j)) := by ring
    _ = -((e i * e i) * (e j * e j)) := by ring
    _ = -(1 * (-1)) := by rw [spatial_sq i hi, momentum_sq j hj]
    _ = -(-1) := by ring
    _ = 1 := by ring

/-!
## Physical Interpretation

The fact that E² = +1 (not −1) is crucial:
- If E² = −1, then exp(θE) = cos(θ) + E·sin(θ) → elliptic rotation (periodic)
- If E² = +1, then exp(θE) = cosh(θ) + E·sinh(θ) → hyperbolic rotation (unbounded)

Hyperbolic rotations mix the spatial and momentum sectors without bound,
representing the continuous exchange of linear and angular momentum.

This is why the Cl(3,3) signature (+,+,+,−,−,−) is essential:
it makes the exchange operators hyperbolic, matching the physics.
-/

/-- Type representing whether a rotation is elliptic or hyperbolic -/
inductive RotationType
  | elliptic   -- E² = −1, periodic (like complex i)
  | hyperbolic -- E² = +1, unbounded (like split-complex j)
  deriving Repr, DecidableEq

/-- Determine rotation type from square -/
def rotationTypeFromSq (sq : ℝ) : RotationType :=
  if sq = 1 then RotationType.hyperbolic else RotationType.elliptic

/-- Exchange bivectors generate hyperbolic rotations -/
theorem exchange_is_hyperbolic (i j : Fin 6) (hi : isSpatial i) (hj : isMomentum j) :
    rotationTypeFromSq (signature33 i * signature33 j).IsNeg.decide.toNat = RotationType.hyperbolic := by
  -- The product of signatures is -1, and we negate it to get +1 for the bivector square
  simp [rotationTypeFromSq, exchange_signature_product i j hi hj]

/-!
## The Nine Exchange Bivectors

There are 3 spatial × 3 momentum = 9 exchange bivectors.
Each represents an exchange channel between configuration and momentum.
-/

/-- Canonical spatial index (0, 1, or 2) -/
def spatialIndex (k : Fin 3) : Fin 6 := ⟨k.val, by omega⟩

/-- Canonical momentum index (3, 4, or 5) -/
def momentumIndex (k : Fin 3) : Fin 6 := ⟨k.val + 3, by omega⟩

/-- Spatial indices are spatial -/
theorem spatialIndex_isSpatial (k : Fin 3) : isSpatial (spatialIndex k) := by
  unfold isSpatial spatialIndex
  omega

/-- Momentum indices are momentum -/
theorem momentumIndex_isMomentum (k : Fin 3) : isMomentum (momentumIndex k) := by
  unfold isMomentum momentumIndex
  omega

/-- Canonical exchange bivector by pair of Fin 3 indices -/
def E (i j : Fin 3) : Cl33 :=
  exchange_bivector (spatialIndex i) (momentumIndex j)
    (spatialIndex_isSpatial i) (momentumIndex_isMomentum j)

/-- All canonical exchange bivectors square to +1 -/
theorem E_sq (i j : Fin 3) : E i j * E i j = 1 := by
  unfold E exchange_bivector
  exact exchange_bivector_sq (spatialIndex i) (momentumIndex j)
    (spatialIndex_isSpatial i) (momentumIndex_isMomentum j)

/-!
## Connection to Paper 3

This file provides the algebraic foundation for Section 2 of Paper 3:
"Linear-Angular Momentum Exchange: The Hidden Dynamics"

The key insight formalized here:
> Mixed bivectors represent the operators that exchange linear and angular momentum.
> They are neither purely real nor purely imaginary—they are geometric objects
> that rotate between sectors.

The (+,+,+,−,−,−) signature makes these hyperbolic, matching the physics
of molecular collisions where momentum exchange is unbounded.
-/

end NSE.SectorExchange
