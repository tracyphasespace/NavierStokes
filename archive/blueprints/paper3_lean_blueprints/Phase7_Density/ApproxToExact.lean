import Mathlib
import Phase7_Density.Interfaces

/-!
# Phase 7 (Paper 3): Approximation → Exactness (functional analysis)

This file provides the analytic mechanism to replace the paper-2 "≈" step by "=".

The key pattern you want in Paper 3 is:

1. Work inside the scleronomic subspace `ker(D)` (closed).
2. Consider the restricted projection `projOnKer : ker(D) → Velocity`.
3. Prove:
   - (A) the range of `projOnKer` is **closed**, and
   - (B) the range is **dense** in the Clay-admissible velocity space.
4. Conclude: range = entire Clay-admissible space, i.e. surjectivity.

In Hilbert/Banach spaces, (A)+(B) ⇒ surjectivity is standard.

[CLAIM NS3.4] [APPROX_TO_EXACT_SURJECTIVITY]
-/

noncomputable section
open scoped Topology

namespace QFD

namespace ScleronomicModel

variable (M : ScleronomicModel)

/-- Closed-range hypothesis for the restricted projection. In your concrete setting, this should be
provable because `proj` is a component/grade projection (bounded idempotent), hence has closed range.

[CLAIM NS3.4a] [CLOSED_RANGE] -/
axiom projOnKer_has_closed_range :
  IsClosed (Set.range (M.projOnKer))

/-- Density hypothesis for the restricted projection range (in the Clay space).
Typically proven using either:
- the soliton density route (Paper 2), or
- the Fourier-symbol right-inverse route (`FourierLift.lean`).

[CLAIM NS3.4b] [DENSE_RANGE] -/
axiom projOnKer_range_dense :
  Dense (Set.range (M.projOnKer))
        { u : M.Velocity | M.ClayAdmissible u }

/-- Upgrade from "dense + closed range" to surjectivity.

[CLAIM NS3.4c] [DENSE_AND_CLOSED_IMPLIES_SURJ] -/
theorem projOnKer_surjective_on_clay :
  { u : M.Velocity | M.ClayAdmissible u } ⊆ Set.range (M.projOnKer) := by
  intro u hu
  -- Since `range(projOnKer)` is closed and dense in the Clay subset,
  -- it must contain that subset (closure = itself).
  -- Proof outline:
  --   have hcl : IsClosed (Set.range M.projOnKer) := projOnKer_has_closed_range ...
  --   have hd  : Dense (Set.range M.projOnKer) ClaySet := projOnKer_range_dense ...
  --   use `hd.closure_eq` and `IsClosed.closure_eq` (or `closure_eq_iff_isClosed`).
  -- TODO: replace with the precise Mathlib lemma chain you prefer.
  sorry

/-- The exact lift existence result, stated at the level of `ker(D)`.

[CLAIM NS3.5] [LIFT_EXISTS_IN_KERD] -/
theorem exists_scleronomic_lift (u0 : M.Velocity) (hu0 : M.ClayAdmissible u0) :
  ∃ Ψ0ker : M.KerD, (M.projOnKer) Ψ0ker = u0 := by
  have : u0 ∈ Set.range (M.projOnKer) := (projOnKer_surjective_on_clay (M := M)) (by
    exact hu0)
  rcases this with ⟨Ψ0ker, rfl⟩
  exact ⟨Ψ0ker, rfl⟩

end ScleronomicModel
end QFD
