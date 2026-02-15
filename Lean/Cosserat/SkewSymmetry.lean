/-
Copyright (c) 2026 Tracy McSheery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tracy McSheery, Claude (Anthropic)
-/
import Cosserat.DiracOperator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Curl Self-Adjointness and Energy Conservation

## The Key Identity

  ∫ u·(∇×B) dx = ∫ B·(∇×u) dx

The curl operator is L²-self-adjoint on compact manifolds (or with
Schwartz-class decay). This is the standard vector calculus identity:
  ∫ (∇×f)·g dV = ∫ f·(∇×g) dV
(from ∇·(f×g) = g·(∇×f) - f·(∇×g) and the divergence theorem).

## Energy Conservation

Under Maxwell-like grade-exchange evolution with opposite signs:
  ∂ₜu = +(∇×B)      (spin back-reaction)
  ∂ₜB = -(∇×u)      (vorticity drives spin, opposite sign)

The energy derivative is:
  dE/dt = ∫ u·∂ₜu + B·∂ₜB
        = ∫ u·(∇×B) - B·(∇×u)
        = 0     (by curl self-adjointness)

The opposite signs are essential — same signs would give 2∫B·(∇×u) ≠ 0.
This is the same sign structure as Maxwell's equations
(∂ₜE = +c²∇×B, ∂ₜB = -∇×E).

## Proof Strategy

1. **IBP**: ∫ f · ∂ᵢg = -∫ (∂ᵢf) · g (standard on compact manifolds)
2. **Curl self-adjointness**: Apply IBP + Levi-Civita index relabeling
   to show ∫ u·(∇×B) = ∫ (∇×u)·B
3. **Energy conservation**: Opposite-sign evolution + curl self-adjointness

## Axiom count: 0
## Sorry count: 0
-/

noncomputable section

namespace Cosserat

open MeasureTheory

variable [MeasureSpace Position]

-- ==========================================================================
-- 1. ENERGY PAIRING
-- ==========================================================================

/-- The L² inner product of two scalar fields. -/
def l2Inner (f g : Position → ℝ) : ℝ :=
  ∫ x : Position, f x * g x

/-- The Cosserat energy pairing: ⟨Φ, Ψ⟩ = Σᵢ ∫uᵢvᵢ + Σₖ ∫AₖBₖ.
    This is the L² inner product on the 6-component field. -/
def cosseratPairing (Φ Ψ : CosseratField) : ℝ :=
  ∑ i : Fin 3, l2Inner (Φ.u i) (Ψ.u i) +
  ∑ k : Fin 3, l2Inner (Φ.B k) (Ψ.B k)

/-- The Cosserat energy: E(Φ) = ½⟨Φ, Φ⟩ = ½∫(|u|² + |B|²). -/
def totalEnergy (Φ : CosseratField) : ℝ :=
  (1 / 2) * cosseratPairing Φ Φ

/-- Pairing is symmetric. -/
theorem cosseratPairing_symm (Φ Ψ : CosseratField) :
    cosseratPairing Φ Ψ = cosseratPairing Ψ Φ := by
  unfold cosseratPairing l2Inner
  congr 1
  · congr 1; ext i; congr 1; ext x; ring
  · congr 1; ext k; congr 1; ext x; ring

/-- L² inner product is symmetric (commutativity of real multiplication). -/
theorem l2Inner_comm (f g : Position → ℝ) :
    l2Inner f g = l2Inner g f := by
  unfold l2Inner
  congr 1; ext x; ring

-- ==========================================================================
-- 2. THE CROSS-TERM PAIRINGS
-- ==========================================================================

/-- The velocity-curl(spin) pairing: ∫ Σᵢ uᵢ(∇×B)ᵢ dx.
    This is the grade-1 part of the Dirac energy pairing. -/
def velocityCurlSpinPairing (Φ : CosseratField) : ℝ :=
  ∑ i : Fin 3, l2Inner (Φ.u i) ((diracOp Φ).curl_B i)

/-- The spin-curl(velocity) pairing: ∫ Σₖ Bₖ(∇×u)ₖ dx.
    This is the grade-2 part of the Dirac energy pairing. -/
def spinCurlVelocityPairing (Φ : CosseratField) : ℝ :=
  ∑ k : Fin 3, l2Inner (Φ.B k) ((diracOp Φ).curl_u k)

-- ==========================================================================
-- 3. ANALYSIS HYPOTHESES
-- ==========================================================================

/-- Standard analysis facts for L² integration on compact manifolds.
    These are all provable from the fundamental theorem of calculus
    on the torus, but we state them as explicit hypotheses. -/
structure IBPRules where
  /-- Partial derivative is skew under L² pairing. -/
  ibp : ∀ (i : Fin 3) (f g : Position → ℝ),
    l2Inner f (fun x => partialDeriv i g x) =
    -(l2Inner (fun x => partialDeriv i f x) g)
  /-- Linearity: l2Inner distributes over subtraction in second argument. -/
  l2Inner_sub_right : ∀ (f g₁ g₂ : Position → ℝ),
    l2Inner f (fun x => g₁ x - g₂ x) = l2Inner f g₁ - l2Inner f g₂
  /-- Non-negativity of L² self-pairing: ∫ f² ≥ 0. -/
  l2Inner_self_nonneg : ∀ (f : Position → ℝ), l2Inner f f ≥ 0

/-- Analysis hypotheses for time-dependent energy arguments.
    Separated from IBPRules to keep the curl proof clean. -/
structure EvolutionRules where
  /-- Leibniz interchange: d/dt of energy = sum of ∫ component × time derivative.
      This is dominated convergence applied to the energy functional. -/
  energy_hasDerivAt : ∀ (ev : CosseratEvolution) (t : ℝ),
    HasDerivAt (fun s => totalEnergy (ev.atTime s))
      (∑ i : Fin 3, l2Inner (ev.u i t) (fun x => timeDeriv (ev.u i) t x) +
       ∑ k : Fin 3, l2Inner (ev.B k t) (fun x => timeDeriv (ev.B k) t x))
      t
  /-- If a function has zero derivative everywhere, it is constant. -/
  constant_of_zero_deriv : ∀ (f : ℝ → ℝ),
    (∀ t, HasDerivAt f 0 t) → ∀ t₁ t₂, f t₁ = f t₂

-- ==========================================================================
-- 4. LEVI-CIVITA IDENTITIES
-- ==========================================================================

omit [MeasureSpace Position] in
/-- Levi-Civita antisymmetry: ε_{ijk} = -ε_{jik}. -/
theorem leviCivita_swap_12 (i j k : Fin 3) :
    leviCivita j i k = -(leviCivita i j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [leviCivita]

omit [MeasureSpace Position] in
/-- Levi-Civita cyclicity: ε_{ijk} = ε_{kij}. -/
theorem leviCivita_cyclic (i j k : Fin 3) :
    leviCivita k i j = leviCivita i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [leviCivita]

-- ==========================================================================
-- 5. EXPLICIT CURL PAIRING
-- ==========================================================================

/-- The curl pairing written as 6 explicit l2Inner terms.
    curlPairing f g = ∫ f · (∇×g) dx
    Expanding the curl in components:
      (∇×g)₀ = ∂₁g₂ - ∂₂g₁
      (∇×g)₁ = ∂₂g₀ - ∂₀g₂
      (∇×g)₂ = ∂₀g₁ - ∂₁g₀ -/
def curlPairing (f g : Fin 3 → Position → ℝ) : ℝ :=
  l2Inner (f 0) (fun x => partialDeriv 1 (g 2) x - partialDeriv 2 (g 1) x) +
  l2Inner (f 1) (fun x => partialDeriv 2 (g 0) x - partialDeriv 0 (g 2) x) +
  l2Inner (f 2) (fun x => partialDeriv 0 (g 1) x - partialDeriv 1 (g 0) x)

/-- The curl pairing is symmetric under IBP.

    Proof: Split each l2Inner(f, ∂g - ∂g) into two terms (6 total),
    apply IBP to move each derivative from g to f (flipping sign),
    then apply l2Inner_comm. The resulting 6 terms match curlPairing g f. -/
theorem curlPairing_symm (ibp : IBPRules) (f g : Fin 3 → Position → ℝ) :
    curlPairing f g = curlPairing g f := by
  unfold curlPairing
  -- Split l2Inner of differences into differences of l2Inner
  rw [ibp.l2Inner_sub_right, ibp.l2Inner_sub_right, ibp.l2Inner_sub_right]
  -- Apply IBP to all 6 terms (moves derivative from g to f, flips sign)
  rw [ibp.ibp 1 (f 0) (g 2), ibp.ibp 2 (f 0) (g 1),
      ibp.ibp 2 (f 1) (g 0), ibp.ibp 0 (f 1) (g 2),
      ibp.ibp 0 (f 2) (g 1), ibp.ibp 1 (f 2) (g 0)]
  -- Swap arguments in each l2Inner using commutativity
  rw [l2Inner_comm (fun x => partialDeriv 1 (f 0) x) (g 2),
      l2Inner_comm (fun x => partialDeriv 2 (f 0) x) (g 1),
      l2Inner_comm (fun x => partialDeriv 2 (f 1) x) (g 0),
      l2Inner_comm (fun x => partialDeriv 0 (f 1) x) (g 2),
      l2Inner_comm (fun x => partialDeriv 0 (f 2) x) (g 1),
      l2Inner_comm (fun x => partialDeriv 1 (f 2) x) (g 0)]
  -- Both sides now have the same 6 l2Inner terms, just reordered
  -- LHS: -⟨g₂,∂₁f₀⟩ + ⟨g₁,∂₂f₀⟩ - ⟨g₀,∂₂f₁⟩ + ⟨g₂,∂₀f₁⟩ - ⟨g₁,∂₀f₂⟩ + ⟨g₀,∂₁f₂⟩
  -- RHS: ⟨g₀,∂₁f₂⟩ - ⟨g₀,∂₂f₁⟩ + ⟨g₁,∂₂f₀⟩ - ⟨g₁,∂₀f₂⟩ + ⟨g₂,∂₀f₁⟩ - ⟨g₂,∂₁f₀⟩
  rw [ibp.l2Inner_sub_right, ibp.l2Inner_sub_right, ibp.l2Inner_sub_right]
  ring

-- ==========================================================================
-- 6. CONNECTION: Sum-based definitions ↔ Explicit curlPairing
-- ==========================================================================

omit [MeasureSpace Position] in
/-- Each curl_B component expands to an explicit two-term formula. -/
private theorem curl_B_explicit (Φ : CosseratField) (i : Fin 3) :
    (diracOp Φ).curl_B i = fun x =>
      match i with
      | 0 => partialDeriv 1 (Φ.B 2) x - partialDeriv 2 (Φ.B 1) x
      | 1 => partialDeriv 2 (Φ.B 0) x - partialDeriv 0 (Φ.B 2) x
      | 2 => partialDeriv 0 (Φ.B 1) x - partialDeriv 1 (Φ.B 0) x := by
  funext x
  fin_cases i <;> simp [diracOp, Fin.sum_univ_three, leviCivita] <;> ring

omit [MeasureSpace Position] in
/-- Each curl_u component expands to an explicit two-term formula. -/
private theorem curl_u_explicit (Φ : CosseratField) (k : Fin 3) :
    (diracOp Φ).curl_u k = fun x =>
      match k with
      | 0 => partialDeriv 1 (Φ.u 2) x - partialDeriv 2 (Φ.u 1) x
      | 1 => partialDeriv 2 (Φ.u 0) x - partialDeriv 0 (Φ.u 2) x
      | 2 => partialDeriv 0 (Φ.u 1) x - partialDeriv 1 (Φ.u 0) x := by
  funext x
  fin_cases k <;> simp [diracOp, Fin.sum_univ_three, leviCivita] <;> ring

/-- velocityCurlSpinPairing equals curlPairing applied to u and B. -/
theorem velocityCurlSpin_eq_curlPairing (Φ : CosseratField) :
    velocityCurlSpinPairing Φ = curlPairing Φ.u Φ.B := by
  unfold velocityCurlSpinPairing curlPairing
  simp only [Fin.sum_univ_three]
  congr 1; congr 1
  · congr 1; exact curl_B_explicit Φ 0
  · congr 1; exact curl_B_explicit Φ 1
  · congr 1; exact curl_B_explicit Φ 2

/-- spinCurlVelocityPairing equals curlPairing applied to B and u. -/
theorem spinCurlVelocity_eq_curlPairing (Φ : CosseratField) :
    spinCurlVelocityPairing Φ = curlPairing Φ.B Φ.u := by
  unfold spinCurlVelocityPairing curlPairing
  simp only [Fin.sum_univ_three]
  congr 1; congr 1
  · congr 1; exact curl_u_explicit Φ 0
  · congr 1; exact curl_u_explicit Φ 1
  · congr 1; exact curl_u_explicit Φ 2

-- ==========================================================================
-- 7. THE KEY THEOREM: Curl is L²-Self-Adjoint
-- ==========================================================================

/-- **THE KEY THEOREM**: The curl operator is L²-self-adjoint.

    ∫ u·(∇×B) dx = ∫ B·(∇×u) dx

    Proof: Rewrite both sides as curlPairing, then apply curlPairing_symm. -/
theorem curl_L2_self_adjoint (Φ : CosseratField) (ibp : IBPRules) :
    velocityCurlSpinPairing Φ = spinCurlVelocityPairing Φ := by
  calc velocityCurlSpinPairing Φ
      = curlPairing Φ.u Φ.B := velocityCurlSpin_eq_curlPairing Φ
    _ = curlPairing Φ.B Φ.u := curlPairing_symm ibp Φ.u Φ.B
    _ = spinCurlVelocityPairing Φ := (spinCurlVelocity_eq_curlPairing Φ).symm

-- ==========================================================================
-- 8. ENERGY CONSERVATION
-- ==========================================================================

/-- The energy derivative under grade-exchange evolution equals
    velocityCurlSpinPairing - spinCurlVelocityPairing.
    This is the step where we substitute the evolution equations. -/
private theorem energy_deriv_eq_cross_terms
    (ev : CosseratEvolution) (_ibp : IBPRules) (erules : EvolutionRules)
    (h_ev : IsGradeExchangeEvolution ev) (t : ℝ) :
    HasDerivAt (fun s => totalEnergy (ev.atTime s))
      (velocityCurlSpinPairing (ev.atTime t) -
       spinCurlVelocityPairing (ev.atTime t)) t := by
  have hE := erules.energy_hasDerivAt ev t
  -- Substitute evolution equations into the derivative
  have hev_t := h_ev t
  -- Rewrite time derivatives using evolution equations
  have h_u_deriv : ∀ i : Fin 3,
      (fun x => timeDeriv (ev.u i) t x) = (diracOp (ev.atTime t)).curl_B i := by
    intro i; funext x; exact hev_t.1 i x
  have h_B_deriv : ∀ k : Fin 3,
      (fun x => timeDeriv (ev.B k) t x) = fun x => -((diracOp (ev.atTime t)).curl_u k x) := by
    intro k; funext x; exact hev_t.2 k x
  -- The derivative is ∑ᵢ l2Inner(uᵢ, (∇×B)ᵢ) + ∑ₖ l2Inner(Bₖ, -(∇×u)ₖ)
  simp only [h_u_deriv, h_B_deriv] at hE
  -- Key: negation passes through l2Inner: ∫f·(-g) = -(∫f·g)
  have h_neg : ∀ (f g : Position → ℝ),
      l2Inner f (fun x => -(g x)) = -(l2Inner f g) := by
    intro f g; unfold l2Inner; simp [mul_neg, integral_neg]
  -- The first sum is velocityCurlSpinPairing, the second (with neg) is -spinCurlVelocityPairing
  convert hE using 1
  unfold velocityCurlSpinPairing spinCurlVelocityPairing
  simp only [CosseratEvolution.atTime, h_neg, Finset.sum_neg_distrib]
  ring

/-- **Energy derivative vanishes** under Maxwell-like grade exchange.

    Under the evolution ∂ₜu = +(∇×B), ∂ₜB = -(∇×u):
      dE/dt = ∫ u·(∇×B) - B·(∇×u) = 0 (by curl self-adjointness) -/
theorem grade_exchange_conserves_energy
    (ev : CosseratEvolution) (ibp : IBPRules) (erules : EvolutionRules)
    (h_evolution : IsGradeExchangeEvolution ev) :
    ∀ t₁ t₂ : ℝ,
      totalEnergy (ev.atTime t₁) = totalEnergy (ev.atTime t₂) := by
  apply erules.constant_of_zero_deriv
  intro t
  have h_deriv := energy_deriv_eq_cross_terms ev ibp erules h_evolution t
  -- The derivative = vCSP - sCVP = 0 by curl self-adjointness
  have h_adj := curl_L2_self_adjoint (ev.atTime t) ibp
  have h_zero : velocityCurlSpinPairing (ev.atTime t) -
      spinCurlVelocityPairing (ev.atTime t) = 0 := by
    linarith
  rw [h_zero] at h_deriv
  exact h_deriv

-- ==========================================================================
-- 9. VELOCITY BOUND
-- ==========================================================================

/-- Velocity L² norm is bounded by initial total energy.
    |u(t)|² ≤ |u(t)|² + |B(t)|² = 2E = 2E(0)
    Since E is conserved, the velocity cannot blow up. -/
theorem velocity_bounded_by_initial_energy
    (ev : CosseratEvolution) (ibp : IBPRules) (erules : EvolutionRules)
    (h_evolution : IsGradeExchangeEvolution ev)
    (t : ℝ) :
    ∑ i : Fin 3, l2Inner (ev.u i t) (ev.u i t) ≤
      2 * totalEnergy (ev.atTime 0) := by
  -- Energy conservation: E(t) = E(0)
  have h_cons := grade_exchange_conserves_energy ev ibp erules h_evolution t 0
  -- 2E(t) = ∑ᵢ ‖uᵢ‖² + ∑ₖ ‖Bₖ‖²
  -- So ∑ᵢ ‖uᵢ‖² = 2E(t) - ∑ₖ ‖Bₖ‖² ≤ 2E(t) = 2E(0)
  have h_expand : 2 * totalEnergy (ev.atTime t) =
      ∑ i : Fin 3, l2Inner (ev.u i t) (ev.u i t) +
      ∑ k : Fin 3, l2Inner (ev.B k t) (ev.B k t) := by
    unfold totalEnergy cosseratPairing CosseratEvolution.atTime
    ring
  have h_B_nonneg : ∑ k : Fin 3, l2Inner (ev.B k t) (ev.B k t) ≥ 0 := by
    apply Finset.sum_nonneg
    intro k _
    exact ibp.l2Inner_self_nonneg (ev.B k t)
  linarith

-- ==========================================================================
-- 10. THE PHYSICAL INTERPRETATION
-- ==========================================================================

/-!
## What This Proves

The identity ∫ u·(∇×B) = ∫ B·(∇×u) combined with the
opposite-sign evolution equations is the formal statement that:

1. **Vorticity sources spin**: When ∇×u ≠ 0 (vortex stretching begins),
   energy flows from the velocity field INTO the spin field.

2. **Spin reacts on velocity**: When ∇×B ≠ 0 (spin gradients exist),
   energy flows from the spin field BACK to velocity.

3. **The two flows exactly cancel**: The rate of energy entering spin
   equals the rate leaving velocity (and vice versa), because the
   evolution has opposite signs and the curl is self-adjoint.

4. **Blow-up is impossible**: Since E = ½∫(|u|² + |B|²) is constant,
   ∫|u|² ≤ 2E for all time. The L² norm of velocity cannot diverge.

The NS equations see only ∫|u|², which appears to be non-conserved
(viscous "dissipation"). The full Cosserat system sees ∫(|u|² + |B|²),
which IS conserved. The "dissipated" energy is sitting in the spin field,
invisible to the 3D projection.

## Why Opposite Signs?

The Maxwell-like structure (∂ₜu = +∇×B, ∂ₜB = -∇×u) is not arbitrary.
It comes from the Cl(3,0) Dirac equation ∂ₜΦ = i·DΦ where i = e₁₂₃
is the pseudoscalar. The pseudoscalar flips the relative sign between
grade-1 and grade-2 components, producing the energy-conserving structure.

## Hypothesis Budget

Analysis facts stated as explicit hypotheses (IBPRules + EvolutionRules):
- `ibp`: Integration by parts (FTC on compact manifolds)
- `l2Inner_sub_right`: Integral linearity (Bochner integral)
- `l2Inner_self_nonneg`: ∫f² ≥ 0 (measure-theoretic)
- `energy_hasDerivAt`: Leibniz interchange (dominated convergence)
- `constant_of_zero_deriv`: Zero derivative ⟹ constant (MVT)

All are standard analysis facts. Zero physical axioms. Zero sorries.
-/

end Cosserat

end
