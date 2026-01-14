# Paper 3 Lean Blueprints: Closing the Scleronomic Lift Gap

These files are intentionally **placeholders**: they compile once you connect them to your concrete
Navier–Stokes / Cl(3,3) operator definitions, and they isolate the remaining proof obligations
into small, well-labeled lemmas.

## Why a 3rd paper?
Paper 1 proves global regularity **conditional** on a Scleronomic Lift hypothesis.
Paper 2 sketches an existence proof for the lift using a soliton-density argument but
explicitly notes:
- the construction is **approximate** at the projection step (`Proj(Ψ₀) ≈ u₀`);
- the density/topology step currently depends on **~11 axioms** (e.g. π₃(S³) ≅ ℤ).

Paper 3 can therefore be purely about:
1) upgrading `≈` to `=` via functional analysis (closed range / bounded right-inverse);
2) eliminating the remaining topology axioms, or replacing that route with a purely analytic lift.

## Contents
- `Phase7_Density/Interfaces.lean`:
  A small interface/typeclass so your existing objects can instantiate it without rewriting the paper.
- `Phase7_Density/DensitySolitons.lean`:
  Formal statement of the soliton-density route and how it implies surjectivity of the lift map.
- `Phase7_Density/ApproxToExact.lean`:
  The functional-analysis upgrade from approximation to exact surjectivity.
- `Phase7_Density/FourierLift.lean`:
  Alternative route: define a Fourier-symbol right-inverse (avoids deep algebraic topology).
- `Phase7_Density/TopologicalAxioms.lean`:
  A single place to park the remaining algebraic topology axioms and track their discharge plan.
- `Phase7_Density/ScleronomicLiftTheorem.lean`:
  The master theorem that replaces the Paper 1 `Scleronomic_Lift_Conjecture` axiom.

## How to integrate
1. Copy the `Phase7_Density/` folder into your repo (next to `Phase6_Lift/`).
2. Replace the abstract interface in `Interfaces.lean` with an instance using your actual types:
   `FullState6D`, `VelocityField`, `D`, `SpatialProjection`, and `ClayAdmissible`.
3. In your existing `Phase6_Lift/ScleronomicLift.lean`, replace the axiom with:

   `theorem Scleronomic_Lift_Conjecture := by exact scleronomic_lift_theorem ...`

4. Fill proof holes in the order indicated in `ScleronomicLiftTheorem.lean`.

If you want, I can also draft the exact patch for your Phase6 file once you paste the current
Lean statement of `Scleronomic_Lift_Conjecture`.
