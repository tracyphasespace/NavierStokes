import NavierStokes_Core.Lemma_Viscosity_Emergence
import NavierStokes_Core.Operator_Viscosity
import NavierStokes_Core.Nonlinear_Emergence
import NavierStokes_Core.Dirac_Operator_Identity

/-!
# NavierStokes Core - Geometric Operator Proofs

This module exports:

1. **Principal Symbol Analysis** (Lemma_Viscosity_Emergence)
   - Algebraic identities: (e₀+e₁+e₂)² = 3, (e₃+e₄+e₅)² = -3
   - These are SYMBOL properties, not operator equations

2. **Operator Cross-Term Cancellation** (Operator_Viscosity)
   - Cross-terms vanish when derivatives commute (Schwarz)
   - Uses tensor product Cl33 ⊗ End(A)

3. **Nonlinear Structure** (Nonlinear_Emergence)
   - Commutator [D, Ψ] gives advection-like structure

4. **Operator Identity** (Dirac_Operator_Identity)
   - The MAIN result: D² = Δ_q - Δ_p (ultrahyperbolic)
   - This is an operator equation on functions, NOT "D² = 0"
-/
