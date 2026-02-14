/-
Copyright (c) 2026 Tracy McSheery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tracy McSheery, Claude (Anthropic)
-/
import Phase7_Density.FunctionSpaces

/-!
# Moment Projection: Phase Space → Vector Velocity

This file defines the moment projection operators that extract macroscopic
velocity fields (3-vectors) from microscopic phase-space distributions.

## The Kinetic Theory Connection

The velocity field is the FIRST MOMENT of the phase-space distribution:
  uᵢ(x) = ∫_𝕋³ pᵢ ρ(p) Re(Ψ(x,p)) dp

The stress tensor is the SECOND MOMENT:
  Tᵢⱼ(x) = ∫_𝕋³ pᵢ pⱼ ρ(p) Re(Ψ(x,p)) dp

The advection nonlinearity (u⊗u) emerges from Reynolds decomposition
of the second moment: Tᵢⱼ = uᵢuⱼ + σᵢⱼ.

## Key Design Choice

`momentumCoord` uses `Quotient.out` to extract a real coordinate from
the torus (same pattern as `partialP` and `gradPNormSq` in FunctionSpaces
and EnergyConservation). The integral over the full torus is independent
of representative choice.

## Axiom Count: 0
-/

noncomputable section

open MeasureTheory Topology

namespace QFD.Phase7.MomentProjection

open QFD.Phase7.FunctionSpaces

variable [MeasureSpace Torus3]

/-- Extract real momentum coordinate from torus via quotient representative.
    Uses `Quotient.out` — same pattern as `partialP` in FunctionSpaces.lean. -/
def momentumCoord (p : Torus3) (i : Fin 3) : ℝ :=
  Quotient.out (p i)

/-- Velocity field from first moment of phase-space distribution.
    uᵢ(x) = ∫_𝕋³ pᵢ ρ(p) Re(Ψ(x,p)) dp
    Returns a 3-vector (Position = EuclideanSpace ℝ (Fin 3)) at each point. -/
def velocityMoment (ρ : SmoothWeight) (Ψ : PhaseSpaceField)
    (x : Position) : Position :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
    ∫ p : Torus3, momentumCoord p i * ρ.ρ p * Complex.re (Ψ (x, p)))

/-- Stress tensor: Tᵢⱼ(x) = ∫_𝕋³ pᵢ pⱼ ρ(p) Re(Ψ(x,p)) dp
    This is the second moment — its decomposition gives advection + viscosity. -/
def stressTensor (ρ : SmoothWeight) (Ψ : PhaseSpaceField)
    (x : Position) : Fin 3 → Fin 3 → ℝ :=
  fun i j => ∫ p : Torus3,
    momentumCoord p i * momentumCoord p j * ρ.ρ p * Complex.re (Ψ (x, p))

/-- Time-dependent velocity from evolution.
    Maps a time-dependent phase-space field to ℝ → Position → Position.
    This matches Phase7_Density.PhysicsAxioms.VelocityField by definition. -/
def velocityFromEvolution (ρ : SmoothWeight) (Ψ : ℝ → PhaseSpaceField)
    : ℝ → Position → Position :=
  fun t x => velocityMoment ρ (Ψ t) x

/-- Stress deviation: σᵢⱼ = Tᵢⱼ - uᵢ uⱼ
    This is what remains after subtracting the Reynolds stress.
    The viscosity closure axiom identifies σᵢⱼ with -ν(∂ᵢuⱼ + ∂ⱼuᵢ). -/
def stressDeviation (ρ : SmoothWeight) (Ψ : PhaseSpaceField)
    (x : Position) (i j : Fin 3) : ℝ :=
  stressTensor ρ Ψ x i j -
    (velocityMoment ρ Ψ x) i * (velocityMoment ρ Ψ x) j

end QFD.Phase7.MomentProjection

end
