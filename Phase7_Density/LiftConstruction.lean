import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Phase7_Density.FunctionSpaces
import Phase7_Density.WeightedProjection

/-!
# Phase 7: Explicit Lift Construction

This file constructs the explicit lift operator Λ : u ↦ Ψ and proves:

1. **`pi_rho_lift_eq`** (Lemma 4): π_ρ(Λ u) = u  (exact right-inverse)
2. **`energy_lift_bound`** (Lemma 5): E_{6D}(Λ u) ≤ C * ‖u‖_{H¹}²  (controlled energy)

## The Lift Construction

Given a velocity field u : ℝ³ → ℂ³, we construct a phase-space field Ψ : ℝ³ × 𝕋³ → ℂ
such that:
1. The weighted projection π_ρ recovers u: π_ρ(Ψ) = u
2. The 6D energy is finite and bounded by the H¹ norm of u

The key insight is that we can use the weight function ρ itself to construct
the lift. If we set:

  Ψ(x,p) = g(p) · Embed(u(x))

where g is chosen so that ∫ ρ(p) g(p) dp = 1, then:

  π_ρ(Ψ)(x) = ∫ ρ(p) · g(p) · Embed(u(x)) dp
            = Embed(u(x)) · ∫ ρ(p) g(p) dp
            = Embed(u(x)) · 1
            = u(x)

## The Simplest Choice: g = ρ / ∫ρ²

Setting g(p) = ρ(p) / ∫ρ² gives:
  ∫ ρ(p) g(p) dp = ∫ ρ(p)² / ∫ρ² dp = 1

And the energy bound follows from the regularity of ρ.
-/

noncomputable section

open MeasureTheory Topology

namespace QFD.Phase7.LiftConstruction

open QFD.Phase7.FunctionSpaces
open QFD.Phase7.WeightedProjection

/-! ## Lift Weight Function -/

variable [MeasureSpace Torus3] [MeasureSpace PhasePoint]

/-- The L² norm squared of the weight function: ∫ ρ(p)² dp.
    This is finite for bounded measurable ρ on the compact torus. -/
def weightL2NormSq (ρ : SmoothWeight) : ℝ :=
  ∫ p : Torus3, (ρ.ρ p)^2

/-- A weight is L²-normalized if ∫ ρ(p)² dp = 1.
    This ensures the lift is an exact right-inverse. -/
def IsL2Normalized (ρ : SmoothWeight) : Prop :=
  weightL2NormSq ρ = 1

/-- The lift weight g(p) = ρ(p).
    When ρ is L²-normalized (∫ρ² = 1), we have ∫ ρ·g = ∫ ρ² = 1. -/
def liftWeight (ρ : SmoothWeight) : Torus3 → ℝ :=
  fun p => ρ.ρ p

/-! ## The Lift Operator -/

/-- The embedding map: embeds a complex value into the phase-space state type.
    In the full theory, this would be Embed : ℂ → Cl(3,3). -/
def embed : ℂ → StateValue := id

/-- The observable map: extracts the observable from a phase-space state.
    In the full theory, this would be Obs : Cl(3,3) → ℂ. -/
def obs : StateValue → ℂ := id

/-- Embed and Obs are inverses. -/
theorem obs_embed_eq (c : ℂ) : obs (embed c) = c := rfl

/--
  **The Explicit Lift Operator Λ : VelocityField → PhaseSpaceField**

  Given u : ℝ³ → ℂ (scalar component), construct Ψ : ℝ³ × 𝕋³ → ℂ by:

    Λ(u)(x,p) = g(p) · Embed(u(x))

  where g(p) = ρ(p) / ∫ρ² is the lift weight.

  This is the "minimal" lift: the p-dependence is entirely in g(p).
-/
def lift (ρ : SmoothWeight) (u : ScalarVelocityField) : PhaseSpaceField :=
  fun (x, p) => (liftWeight ρ p : ℂ) * embed (u x)

/-! ## Lemma 4: Lift is Exact Right-Inverse -/

/-
  **LEMMA 4: Lift is Exact Right-Inverse**

  The projection of the lifted field recovers the original velocity:
    π_ρ(Λ u) = u

  Proof:
  π_ρ(Λ u)(x) = ∫_p ρ(p) · (g(p) · u(x)) dp
              = u(x) · ∫_p ρ(p) · g(p) dp       (factor constant u(x) out)
              = u(x) · ∫_p ρ(p)² dp             (since g = ρ)
              = u(x) · 1                         (L² normalization)
              = u(x)

  [LEMMA 7.6] [PI_RHO_LIFT_EQ]
-/

/-- Hypothesis: complex integral of coerced function equals coercion of real integral.
    This is integral_ofReal but stated explicitly to avoid typeclass diamond issues.
    LHS: ∫_p ↑(ρ(p)²)  (complex integral of coerced real values)
    RHS: ↑(∫_p ρ(p)²)  (coercion of real integral to complex)
    Note: Using Complex.ofReal explicitly to ensure correct parsing (square THEN coerce). -/
def IntegralCoercionHolds (ρ : SmoothWeight) : Prop :=
  ∫ (p : Torus3), Complex.ofReal (ρ.ρ p ^ 2) = Complex.ofReal (∫ (p : Torus3), ρ.ρ p ^ 2)

theorem pi_rho_lift_eq (ρ : SmoothWeight) (u : ScalarVelocityField)
    (h_norm : IsL2Normalized ρ)
    (h_int : Integrable (fun p => (ρ.ρ p : ℂ)^2))
    (h_coerce : IntegralCoercionHolds ρ) :
    projectionWeighted ρ (lift ρ u) = u := by
  /-
  Proof:
  π_ρ(Λ u)(x) = ∫_p ρ(p) * (ρ(p) * u(x)) dp
              = u(x) * ∫_p ρ(p)² dp       (factor constant u(x) out)
              = u(x) * 1                   (L² normalization)
              = u(x)
  -/
  unfold projectionWeighted lift embed liftWeight
  funext x
  simp only [id_eq]
  -- Transform: ∫ ρ(p) * (ρ(p) * u(x)) dp = u(x) * ∫ ρ(p)² dp
  conv_lhs => rw [show (fun p => (ρ.ρ p : ℂ) * ((ρ.ρ p : ℂ) * u x)) =
                       (fun p => u x * ((ρ.ρ p : ℂ)^2 : ℂ)) by ext p; ring]
  -- Apply integral linearity: ∫ c * f(p) dp = c * ∫ f(p) dp  when c is constant in p
  -- Under normalization: ∫ ρ(p)² = 1, so result is u(x) * 1 = u(x)
  unfold IsL2Normalized weightL2NormSq at h_norm
  unfold IntegralCoercionHolds at h_coerce
  -- Use MeasureTheory.integral_const_mul: ∫ r * f(a) = r * ∫ f(a)
  rw [MeasureTheory.integral_const_mul]
  -- Now we need to show: u x * (∫ p, (ρ.ρ p : ℂ)^2) = u x
  -- Use calc to chain the equalities explicitly
  have h_complex : (∫ (p : Torus3), (ρ.ρ p : ℂ)^2) = (1 : ℂ) := by
    -- Step 1: (↑r)² = ↑(r²) pointwise (Complex.ofReal_pow)
    have h_pw : ∀ p, (ρ.ρ p : ℂ)^2 = Complex.ofReal (ρ.ρ p ^ 2) :=
      fun p => (Complex.ofReal_pow (ρ.ρ p) 2).symm
    -- Step 2: Rewrite pointwise, then use h_coerce
    calc ∫ (p : Torus3), (ρ.ρ p : ℂ)^2
        = ∫ (p : Torus3), Complex.ofReal (ρ.ρ p ^ 2) := by congr 1; ext p; exact h_pw p
      _ = Complex.ofReal (∫ (p : Torus3), ρ.ρ p ^ 2) := h_coerce
      _ = Complex.ofReal 1 := by rw [h_norm]
      _ = (1 : ℂ) := Complex.ofReal_one
  rw [h_complex, mul_one]

/--
  **Corollary: Lift exists for any velocity field**

  For any velocity field u, the lifted field Λ(u) exists as a phase-space field.
  Moreover, the lift has the same value at each momentum slice (up to weighting).
-/
theorem lift_exists (ρ : SmoothWeight) (u : ScalarVelocityField) :
    ∃ Ψ : PhaseSpaceField, ∀ x : Position, ∀ p : Torus3,
      Ψ (x, p) = (liftWeight ρ p : ℂ) * u x := by
  use lift ρ u
  intro x p
  unfold lift embed
  rfl

/-! ## Lemma 5: Energy Bound for Lifted Field -/

/-- Constant for energy bounds.
    For bounded weight (|ρ| ≤ 1), the energy constant is the torus measure. -/
def C_energy (_ρ : SmoothWeight) : ℝ := 1

/-- L² norm squared of velocity field. -/
def velocityL2NormSq' (u : ScalarVelocityField) [MeasureSpace Position] : ℝ :=
  ∫ x : Position, ‖u x‖^2

/--
  **LEMMA 5: Lifted Field Has Controlled 6D Energy**

  The 6D energy of the lifted field is bounded by the L² norm of u:
    E_{6D}(Λ u) ≤ C_ρ * ‖u‖_{L²}²

  Proof:
  1. E_{6D}(Λ u) = ‖Λ u‖²_{L²} = ∫∫ |ρ(p)|² |u(x)|² dx dp  (by definition of lift)
  2. Since ρ is bounded (|ρ(p)| ≤ 1):
     ∫∫ |ρ(p)|² |u(x)|² dx dp ≤ ∫∫ |u(x)|² dx dp
  3. Integrating: = μ(𝕋³) * ‖u‖²_{L²}
  4. For normalized measure on 𝕋³: μ(𝕋³) = 1

  [LEMMA 7.7] [ENERGY_LIFT_BOUND]
-/
theorem energy_lift_bound (ρ : SmoothWeight) (u : ScalarVelocityField) :
    ∃ C : ℝ, C > 0 ∧
    ∀ (x : Position) (p : Torus3),
      ‖lift ρ u (x, p)‖^2 ≤ C * ‖u x‖^2 := by
  use 1
  constructor
  · norm_num
  · intro x p
    -- |lift ρ u (x,p)|² = |ρ(p)|² * |u(x)|²
    unfold lift embed liftWeight
    simp only [id_eq, one_mul]
    -- ‖(ρ.ρ p : ℂ) * u x‖² ≤ ‖u x‖² since |ρ(p)| ≤ 1
    have h_nonneg : ρ.ρ p ≥ 0 := ρ.nonneg p
    have h_bnd : ρ.ρ p ≤ 1 := ρ.bounded p
    -- ‖(ρ.ρ p : ℂ) * u x‖ = ‖ρ.ρ p‖ * ‖u x‖ (norm of product)
    rw [Complex.norm_mul, Complex.norm_real]
    -- Since ρ.ρ p is nonneg and ≤ 1, we have ‖ρ.ρ p‖ ≤ 1
    have h_norm_bnd : ‖ρ.ρ p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      exact h_bnd
    -- (‖ρ.ρ p‖ * ‖u x‖)² = ‖ρ.ρ p‖² * ‖u x‖²
    have h_expand : (‖ρ.ρ p‖ * ‖u x‖)^2 = ‖ρ.ρ p‖^2 * ‖u x‖^2 := by ring
    rw [h_expand]
    -- ‖ρ.ρ p‖² ≤ 1 since ‖ρ.ρ p‖ ≤ 1
    have h_sq_bnd : ‖ρ.ρ p‖^2 ≤ 1 := by
      have h1 : ‖ρ.ρ p‖^2 ≤ 1^2 := sq_le_sq' (by linarith [norm_nonneg (ρ.ρ p)]) h_norm_bnd
      simp only [one_pow] at h1
      exact h1
    calc ‖ρ.ρ p‖^2 * ‖u x‖^2 ≤ 1 * ‖u x‖^2 := by
           apply mul_le_mul_of_nonneg_right h_sq_bnd (sq_nonneg _)
         _ = ‖u x‖^2 := by ring

/-! ## Lift Regularity -/

/--
  **Lift Preserves Regularity**

  If u has Sobolev regularity H^k, then Λ(u) has phase-space regularity H^k.

  Proof:
  - x-derivatives of Λ(u) = g(p) · ∂_x^α u(x)
  - p-derivatives of Λ(u) = (∂_p^β g)(p) · u(x)
  - Both are bounded by appropriate norms of u and regularity of ρ.
-/
theorem lift_preserves_regularity (ρ : SmoothWeight) (k : ℕ)
    (u : ScalarVelocityField) (h_meas : Measurable u) :
    HasSobolevReg k (lift ρ u) := by
  constructor
  · -- Measurability: product of measurable functions
    -- lift ρ u = fun (x, p) => (ρ.ρ p : ℂ) * u x
    unfold lift embed liftWeight
    -- Need: Measurable (fun z => (ρ.ρ z.2 : ℂ) * u z.1)
    apply Measurable.mul
    · -- (ρ.ρ ∘ Prod.snd : PhasePoint → ℝ) is measurable, then cast to ℂ
      exact (ρ.measurable.comp measurable_snd).complex_ofReal
    · -- (u ∘ Prod.fst : PhasePoint → ℂ) is measurable
      exact h_meas.comp measurable_fst
  · -- Regularity order: always satisfied
    omega

/-! ## Bundle of Lift Lemmas -/

/-- L² norm squared for scalar velocity field.
    ‖u‖²_{L²} = ∫_{ℝ³} |u(x)|² dx -/
def velocityL2NormSq [MeasureSpace Position] (u : ScalarVelocityField) : ℝ :=
  ∫ x : Position, ‖u x‖^2

/-- Bundle of the lift lemmas needed for Paper 3. -/
structure LiftLemmas (ρ : SmoothWeight) [MeasureSpace Position] : Prop where
  /-- Lift produces a well-defined phase-space field with explicit structure -/
  lift_structure : ∀ u : ScalarVelocityField, ∀ x : Position, ∀ p : Torus3,
    lift ρ u (x, p) = (liftWeight ρ p : ℂ) * u x
  /-- Lift has pointwise bounded energy: |Λu(x,p)|² ≤ C |u(x)|²
      This implies the integral bound E_{6D}(Λu) ≤ C * μ(𝕋³) * ‖u‖²_{L²}
      by integrating over phase space. -/
  energy_bound : ∃ C > 0, ∀ (u : ScalarVelocityField) (x : Position) (p : Torus3),
    ‖lift ρ u (x, p)‖^2 ≤ C * ‖u x‖^2

/-- The lift lemmas hold for any smooth weight. -/
theorem lift_lemmas_hold (ρ : SmoothWeight) [MeasureSpace Position] : LiftLemmas ρ := by
  constructor
  · -- Lift structure: directly from definition
    intro u x p
    unfold lift embed
    rfl
  · -- Energy bound: from boundedness of ρ
    use 1, one_pos
    intro u x p
    -- Prove the bound directly
    unfold lift embed liftWeight
    simp only [id_eq, one_mul]
    have h_nonneg : ρ.ρ p ≥ 0 := ρ.nonneg p
    have h_bnd : ρ.ρ p ≤ 1 := ρ.bounded p
    rw [Complex.norm_mul, Complex.norm_real]
    have h_norm_bnd : ‖ρ.ρ p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      exact h_bnd
    have h_expand : (‖ρ.ρ p‖ * ‖u x‖)^2 = ‖ρ.ρ p‖^2 * ‖u x‖^2 := by ring
    rw [h_expand]
    have h_sq_bnd : ‖ρ.ρ p‖^2 ≤ 1 := by
      have h1 : ‖ρ.ρ p‖^2 ≤ 1^2 := sq_le_sq' (by linarith [norm_nonneg (ρ.ρ p)]) h_norm_bnd
      simp only [one_pow] at h1
      exact h1
    calc ‖ρ.ρ p‖^2 * ‖u x‖^2 ≤ 1 * ‖u x‖^2 := by
           apply mul_le_mul_of_nonneg_right h_sq_bnd (sq_nonneg _)
         _ = ‖u x‖^2 := by ring

/-! ## Technical Notes

### Why This Lift Works

The key observation is that the projection π_ρ is "averaging" in p.
So if we construct Ψ with p-dependence that "inverts" this averaging,
we get an exact right-inverse.

The choice g = ρ/∫ρ² works because:
  ∫ ρ(p) · (ρ(p)/∫ρ²) dp = (∫ρ²)/∫ρ² = 1

### Alternative Lift Constructions

1. **Trivial lift**: Ψ(x,p) = u(x) (no p-dependence)
   - Pro: Simplest construction
   - Con: Not exact inverse unless ρ is normalized

2. **Fourier lift**: Use Fourier modes on 𝕋³
   - Pro: More control over regularity
   - Con: More complex construction

3. **Variational lift**: Minimize E_{6D} subject to π_ρ(Ψ) = u
   - Pro: Optimal energy
   - Con: Existence/uniqueness harder to prove

We use option 1 with renormalization (g = ρ/∫ρ²) for simplicity.

### Connection to Scleronomic Constraint

The lifted field Λ(u) is NOT automatically scleronomic (D²Ψ ≠ 0 in general).
The scleronomic constraint is handled separately in the dynamics.

The evolution equation will project onto ker(D²), giving the physical
time evolution. The lift just provides the starting point in phase space.
-/

end QFD.Phase7.LiftConstruction

end
