import Mathlib
import Phase7_Density.Interfaces
import Phase7_Density.TopologicalAxioms

/-!
# Phase 7 (Paper 3): Density route (solitons ⇒ lift surjectivity)

Paper 2's constructive proof sketch uses a soliton superposition
`Ψ₀ = ∑ cᵢ Ψᵢ` whose projection approximates `u₀`. The missing step is to upgrade:

`Proj(Ψ₀) ≈ u₀`  →  `∃ Ψ₀, Proj(Ψ₀) = u₀`,

and to isolate/remove the topology axioms used to justify density.

This file states the density theorems *in functional-analytic form*.

[CLAIM NS3.1] [SCLERONOMIC_LIFT_EXISTENCE]
-/

noncomputable section
open scoped Topology

namespace QFD

namespace ScleronomicModel

variable (M : ScleronomicModel)

-- ---------------------------------------------------------------------------
-- 1) Abstract "soliton dictionary" and its properties
-- ---------------------------------------------------------------------------

/-- A designated set of *stable soliton* states (Paper 2). Replace with your concrete type:
e.g. a family parameterized by centers, scales, and winding/charge integers. -/
constant Soliton : Set M.State

/-- Solitons are scleronomic. (Holds for your stable/vacuum modes.) -/
axiom soliton_is_scleronomic : ∀ {Ψ : M.State}, Ψ ∈ Soliton (M := M) → M.IsScleronomic Ψ

/-- **Density in the scleronomic subspace**: the closed linear span of solitons is `ker(D)`.

This is the "Density of States" claim from Paper 2, but stated as a standard Hilbert-space fact.

[CLAIM NS3.2] [DENSITY_OF_SOLITONS_IN_KERD] -/
axiom soliton_span_dense_in_kerD :
  Dense ((Submodule.span ℝ (Soliton (M := M))).carrier) (M.KerD : Set M.State)

-- ---------------------------------------------------------------------------
-- 2) From soliton density to density of projected velocities
-- ---------------------------------------------------------------------------

/-- Projected soliton velocities (the "dictionary" on the 3D side). -/
def SolitonVelocity : Set M.Velocity := M.proj '' (Soliton (M := M))

/-- **Density of projected solitons in the Clay-admissible velocity space**.

Depending on your route, you can prove this either by:
- a direct analytic approximation argument (preferred for Clay completeness), or
- the topology/quantization route (Paper 2), plus functional-analytic closure lemmas.

[CLAIM NS3.3] [DENSITY_OF_SOLITON_VELOCITIES] -/
axiom soliton_velocity_dense :
  Dense (Submodule.span ℝ (SolitonVelocity (M := M)) : Set M.Velocity)
        { u : M.Velocity | M.ClayAdmissible u }

end ScleronomicModel
end QFD
