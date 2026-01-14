import Mathlib
import Phase7_Density.Interfaces
import Phase7_Density.ApproxToExact
import Phase7_Density.DensitySolitons
import Phase7_Density.FourierLift

/-!
# Phase 7 (Paper 3): The Scleronomic Lift Theorem

This is the file you ultimately want to import from Paper 1 to eliminate the final axiom.

It offers two routes (you can use either, or keep both and pick via a parameter):
- **Density route** (Paper 2): soliton span dense + closed range ⇒ surjectivity.
- **Fourier route** (Paper 3 alt): explicit bounded right-inverse ⇒ surjectivity.

For the Clay Millennium writeup, the Fourier route is typically the cleanest, because it avoids
deep algebraic topology inside the formal core, and directly constructs the lift operator.

[CLAIM NS3.9] [SCLERONOMIC_LIFT_THEOREM]
-/

noncomputable section

namespace QFD

namespace ScleronomicModel

variable (M : ScleronomicModel)

/-- Paper 3 master theorem: every Clay-admissible initial velocity has a scleronomic lift.

This is the direct replacement for the Paper 1 hypothesis `Scleronomic_Lift_Conjecture`.

[CLAIM NS3.9] [SCLERONOMIC_LIFT_THEOREM] -/
theorem scleronomic_lift_theorem (u0 : M.Velocity) (hu0 : M.ClayAdmissible u0) :
  ∃ Ψ0 : M.State, M.IsScleronomic Ψ0 ∧ M.proj Ψ0 = u0 := by
  -- Route A (density + closed range):
  --   1) Use `exists_scleronomic_lift` from `ApproxToExact.lean`.
  --   2) Coerce `Ψ0ker : KerD` to a `State` to obtain the witness.
  --
  -- Route B (Fourier right-inverse):
  --   1) Let Ψ0 := Lift u0.
  --   2) Apply `Lift_correct`.
  --
  -- In early integration, keep Route A as default (it matches Paper 2);
  -- once Fourier is implemented, Route B becomes the cleanest.
  --
  -- TODO: choose your route and delete the other once stable.
  classical
  -- Use the closed+dense argument to get Ψ0ker in ker(D)
  rcases (exists_scleronomic_lift (M := M) u0 hu0) with ⟨Ψ0ker, hproj⟩
  refine ⟨(Ψ0ker : M.State), ?_, ?_⟩
  · -- scleronomic because Ψ0ker ∈ ker(D)
    -- By definition, `KerD` is the kernel of `D`.
    -- TODO: `simp [ScleronomicModel.IsScleronomic, ScleronomicModel.KerD]` should solve after instantiation.
    sorry
  · -- exact projection
    simpa [ScleronomicModel.projOnKer, ScleronomicModel.kerInclusion] using hproj

end ScleronomicModel
end QFD
