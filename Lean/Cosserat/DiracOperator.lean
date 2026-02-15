/-
Copyright (c) 2026 Tracy McSheery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tracy McSheery, Claude (Anthropic)
-/
import Cosserat.GradeDecomposition
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Dirac Operator on Cl(3,0)-Valued Fields

The Dirac operator D = Σᵢ eᵢ∂ᵢ acts on fields valued in Cl(3,0).
It couples vector and bivector grades:

  D(grade-1) → grade-0 ⊕ grade-2    (divergence + curl)
  D(grade-2) → grade-1 ⊕ grade-3    (back-reaction + pseudoscalar)

For divergence-free, pseudoscalar-free fields:
  D maps grade-1 ↔ grade-2 exclusively (pure grade exchange).

## Key Properties
- D is a first-order differential operator
- D² = -∇² (Laplacian with sign, since all signatures are +1)
- D is skew-symmetric under L² inner product on compact manifolds

## Working in components
Since CliffordAlgebra Q is not a NormedSpace in Mathlib, we work with
component fields: a CosseratField is 6 real-valued functions (3 velocity
+ 3 spin components). The Dirac operator acts on components and the
Clifford multiplication gives the grade coupling.

## Axiom count: 0
## Sorry count: 0 (this file is definitions only)
-/

noncomputable section

namespace Cosserat

open MeasureTheory

-- ==========================================================================
-- 1. SPATIAL TYPES
-- ==========================================================================

/-- Position type: 3D Euclidean space. -/
abbrev Position := EuclideanSpace ℝ (Fin 3)

/-- A Cosserat field: position-dependent mixed-grade state.
    Stores 6 component functions: 3 velocity + 3 spin. -/
structure CosseratField where
  /-- Velocity components uᵢ(x) — grade 1 -/
  u : Fin 3 → Position → ℝ
  /-- Spin components Bₖ(x) — grade 2 (as axial vector via Hodge dual) -/
  B : Fin 3 → Position → ℝ

/-- Total energy density at a point: |u|² + |B|² -/
def CosseratField.energyDensity (Φ : CosseratField) (x : Position) : ℝ :=
  ∑ i : Fin 3, (Φ.u i x) ^ 2 + ∑ k : Fin 3, (Φ.B k x) ^ 2

/-- Energy density is non-negative. -/
theorem CosseratField.energyDensity_nonneg (Φ : CosseratField) (x : Position) :
    Φ.energyDensity x ≥ 0 := by
  unfold energyDensity
  apply add_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

-- ==========================================================================
-- 2. THE DIRAC OPERATOR (Component Form)
-- ==========================================================================

/-- Partial derivative of a scalar field in direction i.
    Uses Mathlib's fderiv; returns 0 when not differentiable. -/
def partialDeriv (i : Fin 3) (f : Position → ℝ) (x : Position) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The Dirac operator applied to a CosseratField.
    D(u + B) has four grade components. We compute them explicitly.

    Grade-0: ∇·u = Σᵢ ∂ᵢuᵢ (divergence)
    Grade-1: (D·B)ᵢ = Σⱼₖ εᵢⱼₖ ∂ⱼBₖ (curl of spin = back-reaction on velocity)
    Grade-2: (∇∧u)ₖ = Σᵢⱼ εₖᵢⱼ ∂ᵢuⱼ (curl of velocity = spin source)
    Grade-3: ∇·B̃ (divergence of B as pseudovector)

    For the Cosserat fluid:
    - Grade-0 vanishes by incompressibility (∇·u = 0)
    - Grade-3 vanishes by assumption (no magnetic monopoles)
    - The remaining Grade-1 ↔ Grade-2 coupling IS the grade exchange. -/
structure DiracResult where
  /-- Grade-0: divergence of velocity -/
  div_u : Position → ℝ
  /-- Grade-1: curl of spin (back-reaction force on velocity) -/
  curl_B : Fin 3 → Position → ℝ
  /-- Grade-2: curl of velocity (spin source from vorticity) -/
  curl_u : Fin 3 → Position → ℝ
  /-- Grade-3: divergence of spin (pseudoscalar) -/
  div_B : Position → ℝ

/-- Levi-Civita symbol for 3D. -/
def leviCivita : Fin 3 → Fin 3 → Fin 3 → ℝ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

/-- Compute the Dirac operator on a CosseratField. -/
def diracOp (Φ : CosseratField) : DiracResult where
  -- Grade-0: ∇·u = Σᵢ ∂ᵢuᵢ
  div_u := fun x => ∑ i : Fin 3, partialDeriv i (Φ.u i) x
  -- Grade-1: (∇×B)ᵢ = Σⱼₖ εᵢⱼₖ ∂ⱼBₖ
  curl_B := fun i x => ∑ j : Fin 3, ∑ k : Fin 3,
    leviCivita i j k * partialDeriv j (Φ.B k) x
  -- Grade-2: (∇×u)ₖ = Σᵢⱼ εₖᵢⱼ ∂ᵢuⱼ
  curl_u := fun k x => ∑ i : Fin 3, ∑ j : Fin 3,
    leviCivita k i j * partialDeriv i (Φ.u j) x
  -- Grade-3: ∇·B = Σₖ ∂ₖBₖ
  div_B := fun x => ∑ k : Fin 3, partialDeriv k (Φ.B k) x

/-- Divergence-free condition: the grade-0 output of D vanishes.
    ∇·u = 0 (incompressibility). -/
def IsDivFree (Φ : CosseratField) : Prop :=
  ∀ x : Position, (diracOp Φ).div_u x = 0

/-- Pseudoscalar-free condition: the grade-3 output of D vanishes.
    ∇·B = 0 (no monopole sources). -/
def IsMonopoleFree (Φ : CosseratField) : Prop :=
  ∀ x : Position, (diracOp Φ).div_B x = 0

/-- Pure grade exchange: both grade-0 and grade-3 vanish.
    D maps grade-1 ↔ grade-2 exclusively. -/
def IsPureGradeExchange (Φ : CosseratField) : Prop :=
  IsDivFree Φ ∧ IsMonopoleFree Φ

-- ==========================================================================
-- 3. THE COSSERAT EVOLUTION EQUATION
-- ==========================================================================

/-- Time derivative of a component field. -/
def timeDeriv (f : ℝ → Position → ℝ) (t : ℝ) (x : Position) : ℝ :=
  fderiv ℝ (fun s => f s x) t 1

/-- Time-dependent Cosserat field. -/
structure CosseratEvolution where
  /-- Velocity components uᵢ(t,x) -/
  u : Fin 3 → ℝ → Position → ℝ
  /-- Spin components Bₖ(t,x) -/
  B : Fin 3 → ℝ → Position → ℝ

/-- Extract the field at a fixed time. -/
def CosseratEvolution.atTime (ev : CosseratEvolution) (t : ℝ) : CosseratField where
  u := fun i => ev.u i t
  B := fun k => ev.B k t

/-- Grade-exchange evolution (Maxwell-like, opposite signs).
    The signs must be OPPOSITE for energy conservation, exactly as in
    Maxwell's equations (∂ₜE = +∇×B, ∂ₜB = -∇×E):
      ∂ₜuᵢ = +(∇×B)ᵢ     (spin back-reaction drives velocity)
      ∂ₜBₖ = -(∇×u)ₖ     (vorticity drives spin, with sign flip)
    Energy conservation: dE/dt = ∫u·(∇×B) - ∫B·(∇×u) = 0
    because ∫f·(∇×g) = ∫(∇×f)·g (curl is L²-self-adjoint via IBP). -/
def IsGradeExchangeEvolution (ev : CosseratEvolution) : Prop :=
  ∀ t : ℝ,
    -- Velocity evolves by + curl of spin
    (∀ i : Fin 3, ∀ x : Position,
      timeDeriv (ev.u i) t x = (diracOp (ev.atTime t)).curl_B i x) ∧
    -- Spin evolves by - curl of velocity (opposite sign!)
    (∀ k : Fin 3, ∀ x : Position,
      timeDeriv (ev.B k) t x = -(diracOp (ev.atTime t)).curl_u k x)

end Cosserat

end
