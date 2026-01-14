import Phase1_Foundation.Cl33
import Phase1_Foundation.BasisOperations
import Phase1_Foundation.BasisReduction

set_option linter.unusedSimpArgs false

/-!
# Principal Symbol Analysis: Clifford Algebra Structure

**IMPORTANT**: This file proves ALGEBRAIC identities about Clifford elements,
NOT operator identities on functions.

## What This File Proves

The identity `(e₀ + e₁ + e₂)² = 3` is a Clifford algebra identity.
This relates to the **principal symbol** of the gradient operator.

**This is NOT** the same as claiming "D² = 0" or "the Laplacian = 3".

## Correct Interpretation

- `grad_q_squared`: `(e₀ + e₁ + e₂)² = 3` as an element of Cl33
- `grad_p_squared`: `(e₃ + e₄ + e₅)² = -3` as an element of Cl33
- These show the SYMBOL structure has signature (+3) and (-3)

## The Actual Operator Identity

The operator identity `D² = Δ_q - Δ_p` is proven in `Dirac_Operator_Identity.lean`
where D acts on functions and derivatives are modeled as linear operators.

## Proof Strategy

The proof expands (e₀ + e₁ + e₂)² using:
- Diagonal terms: eᵢ² = signature(i) = ±1 (from basis_sq)
- Cross terms: eᵢeⱼ + eⱼeᵢ = 0 for i ≠ j (from generators_anticommute)

This leaves: 1+1+1 = 3 for spatial, (-1)+(-1)+(-1) = -3 for momentum.
-/

namespace QFD.GA

open QFD.GA
open QFD.GA.BasisReduction
open CliffordAlgebra

/-! ## Helper Lemmas: Anticommutator Cancellation

We directly use `generators_anticommute` from Cl33.lean which proves:
  ι33(basis_vector i) * ι33(basis_vector j) + ι33(basis_vector j) * ι33(basis_vector i) = 0
-/

/-- The anticommutator of distinct basis vectors vanishes: eᵢeⱼ + eⱼeᵢ = 0 -/
theorem anticommutator_zero {i j : Fin 6} (h : i ≠ j) :
    e i * e j + e j * e i = 0 := by
  unfold e
  exact generators_anticommute i j h

/-- Specific instances for spatial basis vectors -/
lemma e01_anticomm : e 0 * e 1 + e 1 * e 0 = 0 :=
  anticommutator_zero (by decide)

lemma e02_anticomm : e 0 * e 2 + e 2 * e 0 = 0 :=
  anticommutator_zero (by decide)

lemma e12_anticomm : e 1 * e 2 + e 2 * e 1 = 0 :=
  anticommutator_zero (by decide)

/-- Specific instances for momentum basis vectors -/
lemma e34_anticomm : e 3 * e 4 + e 4 * e 3 = 0 :=
  anticommutator_zero (by decide)

lemma e35_anticomm : e 3 * e 5 + e 5 * e 3 = 0 :=
  anticommutator_zero (by decide)

lemma e45_anticomm : e 4 * e 5 + e 5 * e 4 = 0 :=
  anticommutator_zero (by decide)

/-! ## The Configuration Gradient and its Square -/

/-- The Configuration Gradient ∇q (sum of e_0, e_1, e_2) -/
def grad_q : Cl33 := e 0 + e 1 + e 2

/-- The Momentum Gradient ∇p (sum of e_3, e_4, e_5) -/
def grad_p : Cl33 := e 3 + e 4 + e 5

/-- The Total Dirac Operator D = ∇q + ∇p -/
def D : Cl33 := grad_q + grad_p

/-! ## Principal Symbol Computation -/

/-- **THEOREM**: The spatial gradient symbol squared equals 3

This is an ALGEBRAIC identity in Cl33:
  (e₀ + e₁ + e₂)² = e₀² + e₁² + e₂² + (anticommutators) = 1 + 1 + 1 + 0 = 3

**Interpretation**: The principal symbol of Δ_q has trace +3 from the (+,+,+) signature.
This does NOT mean "Δ_q = 3" - it means the symbol structure encodes 3 spatial dimensions.
-/
theorem grad_q_squared : grad_q * grad_q = (3 : Cl33) := by
  unfold grad_q
  -- Expand (e0 + e1 + e2) * (e0 + e1 + e2)
  simp only [add_mul, mul_add]
  -- Simplify squares
  simp only [e0_square, e1_square, e2_square]
  -- The anticommutators vanish
  have h01 : e 0 * e 1 + e 1 * e 0 = 0 := e01_anticomm
  have h02 : e 0 * e 2 + e 2 * e 0 = 0 := e02_anticomm
  have h12 : e 1 * e 2 + e 2 * e 1 = 0 := e12_anticomm
  -- Now manually combine: after simp, goal is algebraic combination of 1s and cross terms
  -- The form is: 1 + (cross01) + (cross02) + (cross10) + 1 + (cross12) + (cross20) + (cross21) + 1
  -- We use ac_refl or manual addition rewriting
  -- First, pair up the anticommutators and use that they're 0
  calc 1 + e 1 * e 0 + e 2 * e 0 + (e 0 * e 1 + 1 + e 2 * e 1) + (e 0 * e 2 + e 1 * e 2 + 1)
      = 1 + 1 + 1 + (e 0 * e 1 + e 1 * e 0) + (e 0 * e 2 + e 2 * e 0) + (e 1 * e 2 + e 2 * e 1) := by
        simp only [add_comm, add_left_comm, add_assoc]
    _ = 1 + 1 + 1 + 0 + 0 + 0 := by rw [h01, h02, h12]
    _ = (3 : Cl33) := by norm_num

/-- **THEOREM**: The momentum gradient symbol squared equals -3

Algebraic identity in Cl33: (e₃ + e₄ + e₅)² = (-1) + (-1) + (-1) = -3
The (-,-,-) signature contributes -3 to the symbol trace.
-/
theorem grad_p_squared : grad_p * grad_p = (-3 : Cl33) := by
  unfold grad_p
  simp only [add_mul, mul_add]
  simp only [e3_square, e4_square, e5_square]
  have h34 : e 3 * e 4 + e 4 * e 3 = 0 := e34_anticomm
  have h35 : e 3 * e 5 + e 5 * e 3 = 0 := e35_anticomm
  have h45 : e 4 * e 5 + e 5 * e 4 = 0 := e45_anticomm
  calc -1 + e 4 * e 3 + e 5 * e 3 + (e 3 * e 4 + -1 + e 5 * e 4) + (e 3 * e 5 + e 4 * e 5 + -1)
      = -1 + (-1) + (-1) + (e 3 * e 4 + e 4 * e 3) + (e 3 * e 5 + e 5 * e 3) + (e 4 * e 5 + e 5 * e 4) := by
        simp only [add_comm, add_left_comm, add_assoc]
    _ = -1 + (-1) + (-1) + 0 + 0 + 0 := by rw [h34, h35, h45]
    _ = (-3 : Cl33) := by norm_num

/-! ## Symbol Decomposition -/

/-- **THEOREM**: The Dirac symbol squared decomposes algebraically

This shows: (grad_q + grad_p)² = 3 + (-3) + (cross-sector terms)
The 3 + (-3) = 0 is the SYMBOL trace cancellation, not an operator equation.

See `Dirac_Operator_Identity.lean` for the actual operator identity D² = Δ_q - Δ_p.
-/
theorem Viscosity_Is_Geometric :
    D * D = (3 : Cl33) + (-3 : Cl33) + (grad_q * grad_p + grad_p * grad_q) := by
  unfold D
  -- (grad_q + grad_p) * (grad_q + grad_p) = grad_q² + grad_q*grad_p + grad_p*grad_q + grad_p²
  simp only [add_mul, mul_add]
  rw [grad_q_squared, grad_p_squared]
  -- Now need: 3 + grad_q*grad_p + grad_p*grad_q + (-3) = 3 + (-3) + (grad_q*grad_p + grad_p*grad_q)
  simp only [add_comm, add_left_comm, add_assoc]

/-- **COROLLARY**: The symbol trace is zero

This 3 + (-3) = 0 reflects the balanced (3,3) signature.
It does NOT mean "Δ = 0" - it means the SYMBOL has zero net trace.
-/
theorem Symbol_Trace_Zero : (3 : Cl33) + (-3 : Cl33) = (0 : Cl33) := by
  norm_num

/-- **COROLLARY**: Spatial symbol contribution is 3 -/
theorem Spatial_Symbol_Trace : grad_q * grad_q = (3 : Cl33) := grad_q_squared

/-- **COROLLARY**: After trace cancellation, only cross-sector terms remain

This shows algebraically that the symbol of D² reduces to bivector terms.
The operator interpretation: D² = Δ_q - Δ_p (ultrahyperbolic, NOT zero).
-/
theorem Symbol_Cross_Terms_Only :
    D * D = (grad_q * grad_p + grad_p * grad_q) := by
  rw [Viscosity_Is_Geometric, Symbol_Trace_Zero]
  simp only [zero_add]

end QFD.GA
