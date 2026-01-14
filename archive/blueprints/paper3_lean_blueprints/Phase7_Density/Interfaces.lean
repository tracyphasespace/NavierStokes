import Mathlib

/-!
# Phase 7 (Paper 3): Interfaces for the Scleronomic Lift completion

This file defines a small **interface** that Paper 3 uses, so you can connect the new
functional-analysis/density arguments to your existing Navier–Stokes / Cl(3,3) objects
without rewriting the whole development.

## Key idea
Paper 1 isolates the single remaining gap as `Scleronomic_Lift_Conjecture`.
Paper 3 should prove it by providing a *bounded lift operator* or a *closed-range surjectivity*
argument for the projection restricted to the scleronomic subspace.

All results below are written in terms of:
- a state space `State` (6D fields Ψ),
- a velocity space `Velocity` (3D fields u),
- a linear (or continuous linear) operator `D` (the Cl(3,3) Dirac-like operator),
- a continuous projection `proj : State → Velocity`,
- and a predicate `ClayAdmissible` capturing the Clay initial-data class.

You should later **instantiate** this structure with your concrete definitions:
`FullState6D`, `VelocityField`, `D`, `SpatialProjection`, etc.
-/

noncomputable section

namespace QFD

/-- Interface for the analytic "lift existence" layer of the Navier–Stokes proof. -/
class ScleronomicModel where
  /-- 6D state space (Ψ-fields). -/
  State : Type
  /-- 3D velocity space (u-fields). -/
  Velocity : Type

  -- Linear/metric structure
  [stateNorm : NormedAddCommGroup State]
  [stateSMul : NormedSpace ℝ State]
  [velNorm : NormedAddCommGroup Velocity]
  [velSMul : NormedSpace ℝ Velocity]

  /-- Dirac-like operator (model as continuous linear map for the Paper 3 layer).
  In your concrete development `D` may be a differential operator; you can replace this
  with a graph-closed operator interface later. -/
  D : State →L[ℝ] State

  /-- Projection from 6D state to 3D velocity. -/
  proj : State →L[ℝ] Velocity

  /-- Predicate capturing the Clay-admissible initial-data class. -/
  ClayAdmissible : Velocity → Prop

attribute [instance] ScleronomicModel.stateNorm ScleronomicModel.stateSMul
attribute [instance] ScleronomicModel.velNorm ScleronomicModel.velSMul

namespace ScleronomicModel

variable (M : ScleronomicModel)

/-- Scleronomic states are those in the kernel of `D`. -/
def IsScleronomic (Ψ : M.State) : Prop := M.D Ψ = 0

/-- The scleronomic subspace `ker(D)`. -/
def KerD : Submodule ℝ M.State := M.D.ker

/-- Inclusion `ker(D) → State` as a continuous linear map (built explicitly to avoid relying on
`Submodule.subtypeL` name stability). -/
def kerInclusion : M.KerD →L[ℝ] M.State :=
{ toLinearMap := (M.KerD).subtype
  cont := by
    -- continuity of subtype coercion
    simpa using (continuous_subtype_val : Continuous fun x : M.KerD => (x : M.State)) }

/-- Projection restricted to scleronomic states: `ker(D) → Velocity`. -/
def projOnKer : M.KerD →L[ℝ] M.Velocity := M.proj.comp M.kerInclusion

/-- The lift statement you ultimately need (Paper 1 hypothesis, Paper 3 theorem).

[CLAIM NS3.0] [SCLERONOMIC_LIFT_EXISTENCE] -/
def LiftStatement (u0 : M.Velocity) : Prop :=
  ∃ Ψ0 : M.State, M.IsScleronomic Ψ0 ∧ M.proj Ψ0 = u0

end ScleronomicModel

end QFD
