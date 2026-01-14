import Phase7_Density.PhaseField
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Separation.Basic

/-!
# Phase 7 (Paper 3): The Scleronomic Lift Theorem

## Main Result

**Theorem (Scleronomic Lift)**: If the projection of ker(D) onto velocities has
closed range and is dense in the admissible set, then every admissible velocity
admits a scleronomic lift.

This is a pure functional analysis result:
- `IsClosed (range projOnKer)` + `AdmissibleSet ⊆ closure (range projOnKer)`
- ⟹ `AdmissibleSet ⊆ range projOnKer`

The proof uses only Mathlib's topology, no axioms.

## Mathematical Content

The key insight is that:
1. If a set is closed, then closure(S) = S
2. If S is dense in T, then T ⊆ closure(S)
3. Therefore T ⊆ S

This transforms the density argument into exact surjectivity.
-/

noncomputable section

open Set Topology

namespace QFD.Phase7

namespace ScleronomicModel

variable (M : ScleronomicModel)

/-! ## Core Topological Lemma -/

/-- **Key Lemma**: If range is closed and admissible set is contained in its closure,
    then admissible set is contained in range.

    This is the pure topology part - no PDE analysis needed here. -/
theorem closed_dense_implies_subset
    (h_closed : IsClosed (range M.projOnKer))
    (h_dense : M.AdmissibleSet ⊆ closure (range M.projOnKer)) :
    M.AdmissibleSet ⊆ range M.projOnKer := by
  -- IsClosed means closure = self
  rw [← h_closed.closure_eq]
  exact h_dense

/-! ## The Lift Theorem -/

/-- **Theorem (Paper 3): Scleronomic Lift Existence**

    If:
    1. The range of projOnKer is closed (a functional analysis hypothesis)
    2. Every admissible velocity is in the closure of this range (density)

    Then: Every admissible velocity has a scleronomic lift.

    [CLAIM NS3.10] [SCLERONOMIC_LIFT_FROM_DENSITY]
-/
theorem scleronomic_lift_from_density
    (h_closed : IsClosed (range M.projOnKer))
    (h_dense : M.AdmissibleSet ⊆ closure (range M.projOnKer))
    (u : M.Velocity)
    (hu : M.Admissible u) :
    M.LiftExists u := by
  -- Apply the topological lemma to get u ∈ range(projOnKer)
  have h_in_range : u ∈ range M.projOnKer :=
    closed_dense_implies_subset M h_closed h_dense hu
  -- Extract the preimage: there exists Ψker in KerD such that projOnKer Ψker = u
  obtain ⟨Ψker, hΨ⟩ := h_in_range
  -- Ψker is in KerD, so kerInclusion Ψker is in State and is scleronomic
  use M.kerInclusion Ψker
  constructor
  · -- Scleronomic: D(kerInclusion Ψker) = 0
    -- This follows because Ψker ∈ KerD = D.ker
    show M.D (M.kerInclusion Ψker) = 0
    exact Ψker.property
  · -- Projection matches: proj(kerInclusion Ψker) = u
    -- projOnKer = proj ∘ kerInclusion, so projOnKer Ψker = proj (kerInclusion Ψker)
    exact hΨ

/-! ## Corollaries -/

/-- **Corollary**: Under the density hypotheses, lift exists for all admissible data. -/
theorem lift_exists_for_all_admissible
    (h_closed : IsClosed (range M.projOnKer))
    (h_dense : M.AdmissibleSet ⊆ closure (range M.projOnKer)) :
    ∀ u : M.Velocity, M.Admissible u → M.LiftExists u :=
  fun u hu => scleronomic_lift_from_density M h_closed h_dense u hu

end ScleronomicModel

/-! ## Summary

**What Paper 3 Proves** (this file):

The scleronomic lift exists for all admissible data IF:
1. `IsClosed (range projOnKer)` - range is closed
2. `AdmissibleSet ⊆ closure (range projOnKer)` - density in admissible set

**What Remains to Verify** (for concrete instantiation):

1. The concrete operator D (Dirac in Cl(3,3)) has projOnKer with closed range
2. The soliton/Fourier construction shows density

These are the PDE/functional analysis hypotheses that connect abstract
theory to the Navier-Stokes problem.

**Why This is Mathematically Sound**:

The proof uses only:
- `IsClosed.closure_eq` from Mathlib
- Basic set theory (`⊆` transitivity)
- Subtype coercion

No axioms, no sorries, no `:= True`.
-/

end QFD.Phase7

end
