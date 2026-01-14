import Phase2_Projection.Conservation_Exchange
import Phase2_Projection.Sign_Exchange

/-!
# Phase 2: Scleronomic Projection (Conservation as Exchange)

This module proves the key insight:

**Viscosity in 3D = Conservation in 6D**

The equation D² Ψ = 0 means:
  Δ_q Ψ = Δ_p Ψ

"Spatial curvature equals momentum curvature"

What looks like dissipation (viscous loss) in configuration space
is exactly balanced by structure in momentum space.

## The Metric Sign Flip

The signature (+,+,+,-,-,-) is not just a label - it's an **active operator**.
- A "Source" in q-space becomes a "Sink" in p-space
- The sign flip is the metric doing its job
- No information is lost, only exchanged

## Key Theorems

### Conservation_Exchange.lean
1. `Conservation_Implies_Exchange`: D² = 0 implies Δ_q = Δ_p
2. `Viscosity_Is_Exchange`: Viscous diffusion emerges from 6D conservation

### Sign_Exchange.lean
3. `Metric_Sign_Flip`: The signature enforces Source = Sink
4. `Viscosity_Is_Conservation`: Viscosity coefficient from metric structure
-/
