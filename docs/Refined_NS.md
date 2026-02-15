# Refined NS Regularity Strategy

## Status: The Current Framework's Gap

The existing formalization proves a **conditional** theorem:

> IF a ScleronomicKineticEvolution exists (scleronomic constraint + transport
> + Chapman-Enskog closure + ...), THEN NS has a global weak solution.

The gap: **the hypotheses are mutually inconsistent for generic data.**

Free streaming `∂_t Ψ + p·∇_x Ψ = 0` solved by characteristics gives
`Ψ(t,x,p) = Ψ_0(x - tp, p)`. Computing the momentum Laplacian:

```
Δ_p Ψ(t) = Δ_p Ψ_0 - 2t ∑ᵢ ∂²Ψ_0/∂xᵢ∂pᵢ + t² Δ_x Ψ_0
```

For `Δ_x Ψ = Δ_p Ψ` to hold for all t, we need `Δ_x Ψ_0 = 0` (harmonic
initial data). The scleronomic constraint is **not preserved** by free
streaming transport. The conditional theorem is correct Lean, but the
conditions can't be met for interesting data.

The Clifford algebra (Phases 1-3) is real verified algebra.
The moment derivation (Phase 7) is standard kinetic theory, correctly
formalized. Neither is wrong — they just don't close the regularity gap.

---

## What's Actually Hard About NS Regularity

The 3D incompressible NS equations:

```
∂_t u + (u·∇)u = -∇p + ν Δu,    ∇·u = 0
```

**Known facts:**
- Global weak (Leray-Hopf) solutions exist. Energy: `||u(t)||² + 2ν ∫₀ᵗ ||∇u||² ≤ ||u₀||²`
- Smooth solutions exist locally: on `[0, T*)` for some T* > 0
- In 2D: global regularity proved (Ladyzhenskaya, 1969)
- In 3D: open. Partial regularity (CKN): singular set has parabolic Hausdorff dim ≤ 1

**Why it's hard — the supercritical gap:**

The enstrophy equation (key battleground):
```
d/dt ||ω||² = -ν||∇ω||² + ∫ ω·(ω·∇)u dx
                dissipation      vortex stretching
```

The stretching term `∫ ω·(ω·∇)u` is cubic in u. Using interpolation:
```
|∫ ω·(ω·∇)u| ≤ C ||ω||^(1/2) ||∇ω||^(5/2)
```

vs dissipation `ν||∇ω||²`. The stretching exponent (5/2) beats the
dissipation exponent (2). This is **supercriticality**: the nonlinearity
can potentially overwhelm viscous damping. Closing this gap is the
millennium problem.

In 2D: vortex stretching vanishes identically (ω is scalar, perpendicular
to flow). That's why 2D is solved.

---

## The Core Insight Worth Keeping

NS is derived from the Boltzmann equation via Chapman-Enskog. The
Boltzmann equation has **more structure** than NS:

1. **H-theorem**: `d/dt ∫ f ln f ≤ 0` — entropy monotonically decreases.
   This is an a priori estimate NS doesn't have.

2. **Collision operator is regularizing**: The Boltzmann collision operator
   `Q(f,f)` gains regularity in velocity. Specifically, for hard potentials
   with angular cutoff, `Q(f,f)` maps H^k_v → H^(k+s)_v for some s > 0.

3. **Velocity averaging lemmas** (Golse-Lions-Perthame-Sentis): Velocity
   averages `∫ f(x,v)φ(v) dv` are smoother than f itself. This is free
   regularity from the kinetic structure.

The physical insight: viscosity comes from molecular collisions, and the
collision operator regularizes. NS threw away this regularization when it
replaced the collision operator with a constant ν.

**The question: can we recover this lost regularity?**

---

## Proposed Approach: Collisional Lift

### The Idea

Replace free streaming (which doesn't regularize) with the full Boltzmann
equation (which does). The lift should use the collision operator, not
ignore it.

### Architecture

```
Layer 1: BOLTZMANN EQUATION (6D kinetic, globally well-posed near equilibrium)
    f(x,v,t): phase space distribution
    ∂_t f + v·∇_x f = Q(f,f)
    Q = collision operator (regularizing)
    H-theorem: ∫ f ln f decreasing

Layer 2: HYDRODYNAMIC MOMENTS (3D macroscopic)
    ρ(x,t) = ∫ f dv          (density)
    u(x,t) = (1/ρ) ∫ vf dv   (velocity)
    T(x,t) = (1/3ρ) ∫ |v-u|² f dv  (temperature)

Layer 3: NAVIER-STOKES (projection of Layer 2)
    ∂_t u + (u·∇)u = -∇p + ν Δu + O(Kn²)
    Exact in the limit Kn → 0
```

### The Three Problems To Solve

**Problem 1: Boltzmann global regularity near local Maxwellians**

For data near **global** Maxwellian: SOLVED (Guo, 2003). Smooth solutions
exist globally and converge exponentially to equilibrium.

For data near **local** Maxwellian (what we need for NS lift): OPEN.
The local Maxwellian `M(v; ρ(x), u(x), T(x))` has x-dependent parameters.
Perturbation theory around local Maxwellian requires controlling how ρ, u, T
evolve — which brings us back to NS-type estimates.

**Research direction**: Can we combine Guo's perturbative framework with
the entropy dissipation estimates of Villani (2009) to handle local
Maxwellian data? The key is whether the collision operator regularizes
fast enough to prevent the hydrodynamic fields from developing singularities.

**Problem 2: Regularity transfer through hydrodynamic limit**

Even if Boltzmann solutions are smooth, we need the velocity moments
(density, velocity, temperature) to be smooth **and** to satisfy NS.

Known: Golse-Saint-Raymond (2004) proved that renormalized Boltzmann
solutions converge to Leray-Hopf weak solutions of NS in the incompressible
limit. But weak ≠ smooth.

**Research direction**: Strengthen the convergence. Instead of weak L²
convergence, prove H^k convergence for all k. This requires **uniform
in Kn** Sobolev estimates for the Boltzmann-derived velocity field. The
velocity averaging lemmas give some regularity; the question is whether
they give enough.

**Problem 3: The Chapman-Enskog breakdown**

Chapman-Enskog is a perturbative expansion in Kn (Knudsen number = mean
free path / macroscopic length). At blow-up, gradients → ∞, so the
macroscopic length → 0, and Kn → ∞. The expansion breaks down exactly
where we need it.

**Research direction**: Don't use Chapman-Enskog. Work with the full
Boltzmann equation at fixed Kn > 0. The Boltzmann-derived velocity field
u_Kn satisfies:
```
∂_t u_Kn + (u_Kn·∇)u_Kn = -∇p_Kn + ν Δu_Kn + R_Kn
```
where R_Kn = O(Kn²) is the remainder. If u_Kn is smooth (from Boltzmann
regularity) and R_Kn → 0 strongly enough as Kn → 0, then the limit u
is a smooth NS solution.

**The key estimate**: We need `||R_Kn||_{H^k} → 0` uniformly in time.
This is the hard part — it requires the Boltzmann solution to stay
close to local equilibrium uniformly, which requires the hydrodynamic
fields to stay smooth, which is what we're trying to prove. The argument
must be bootstrapped.

---

## Concrete Research Plan

### Phase A: Formalize Boltzmann Foundations (Lean)

Formalize in Lean what is already known:

1. **Boltzmann equation on T³ × R³** (periodic box, velocity space)
   - Collision operator Q for hard spheres
   - H-theorem: `∫ f ln f` is a Lyapunov functional
   - Local Maxwellian: equilibrium of Q

2. **Velocity averaging lemmas**
   - If `∂_t f + v·∇_x f = g` with f, g ∈ L², then
     `∫ f(x,v)φ(v)dv ∈ H^(1/2)_x`
   - This is a key regularity gain from kinetic structure

3. **Moment equations** (already partially done in Phase 7)
   - Continuity: `∂_t ρ + ∇·(ρu) = 0`
   - Momentum: `∂_t(ρu) + ∇·(ρu⊗u) + ∇p = ∇·σ`
   - Energy: `∂_t E + ∇·((E+p)u) = ∇·(σ·u) + ∇·(κ∇T)`

### Phase B: Near-Equilibrium Boltzmann Regularity

Study whether Guo's (2003) perturbative result can be extended:

4. **Guo's framework**: For `f = M + M^(1/2)·g` with M = global
   Maxwellian, the perturbation g satisfies a dissipative equation.
   Guo proved global H^k bounds on g.

5. **Local Maxwellian perturbation**: For `f = M_local + M_local^(1/2)·g`,
   the perturbation equation has additional terms from ∇_x(ρ, u, T).
   These terms couple back to NS — this is where the bootstrap must happen.

6. **The bootstrap argument** (the core mathematical challenge):
   - Assume u ∈ H^k on [0,T] (smooth NS solution exists locally)
   - Construct Boltzmann solution f near M_local(ρ,u,T) on [0,T]
   - Use collision regularization to prove f is smoother than assumed
   - Extract improved estimates on u from f
   - Close: the improved u estimates extend the existence interval
   - Iterate to T = ∞

### Phase C: The Compactness Argument

7. **Uniform estimates**: Prove that the family {u_Kn}_Kn is uniformly
   bounded in H^k, independent of Kn, for all k.

8. **Strong convergence**: Use Aubin-Lions compactness + the uniform
   estimates to extract a strongly convergent subsequence.

9. **Limit identification**: Show the limit satisfies NS exactly (the
   remainder R_Kn → 0 in H^k).

---

## What Can Be Formalized Now vs What's Open

| Component | Status | Lean Target |
|-----------|--------|-------------|
| Boltzmann equation definition | Standard | Yes — define Q, f, moments |
| H-theorem | Standard | Yes — entropy monotonicity |
| Velocity averaging lemma | Proved (1988) | Yes — H^(1/2) gain |
| Moment derivation (continuity + momentum) | Standard | Already done (Phase 7) |
| Guo perturbative framework | Proved (2003) | Possible but hard |
| Local Maxwellian perturbation | OPEN | Research target |
| Bootstrap argument | OPEN | The prize |
| Hydrodynamic limit regularity | OPEN | Requires bootstrap |

---

## Difficulty Assessment

**Problem 1** (Boltzmann near local Maxwellian): Hard but approachable.
Guo's methods + modern entropy techniques might reach this. Estimated
difficulty: 3-5 years of focused research.

**Problem 2** (Regularity transfer): Very hard. The hydrodynamic limit
community has been working on this for 30 years. The velocity averaging
lemma gives H^(1/2), but NS regularity needs H^(5/2+). Estimated
difficulty: 5-10 years.

**Problem 3** (Bootstrap): This IS the millennium problem, reformulated
in kinetic language. If you can close the bootstrap, you've solved it.
The advantage of the kinetic formulation is that you have more tools
(collision regularization, H-theorem, velocity averaging). The disadvantage
is that you're working in 6D instead of 3D.

**Overall**: This is a genuine research program, not a quick proof.
The kinetic theory route is one of the more promising approaches to NS
regularity (alongside the De Giorgi method, convex integration, and
critical Sobolev space techniques). It has the advantage of physical
motivation and additional structure. It has the disadvantage of
higher-dimensional complexity.

---

## What The Current Lean Infrastructure Provides

The existing 64-file, 3209-job Lean formalization is not wasted:

- **Phase 1-3 (Clifford algebra)**: Genuine verified algebra. Useful for
  representing the Boltzmann collision operator in geometric language.
- **Phase 7 (Function spaces)**: `Torus3`, `PhaseSpaceField`, Laplacians,
  Sobolev spaces — directly reusable for Boltzmann formalization.
- **Phase 7 (Moment derivation)**: Reynolds decomposition, weak NS
  formulation — directly reusable. This IS the Chapman-Enskog derivation.
- **Validation framework**: `HonestyAudit.lean`, `AxiomDependencies.lean`
  — reusable for any new axiom/hypothesis management.

What must change:
- Replace free streaming transport with full Boltzmann equation
- Add collision operator Q(f,f) with regularization properties
- Add H-theorem as a proved consequence (not axiom)
- The scleronomic constraint must be DERIVED from collision equilibrium,
  not assumed

---

## Next Steps

1. **Read Guo (2003)** — "The Boltzmann equation in the whole space."
   Understand the perturbative framework and what estimates it provides.

2. **Read Golse-Saint-Raymond (2004)** — "The Navier-Stokes limit of
   the Boltzmann equation for bounded collision kernels."
   Understand how regularity is lost in the limit.

3. **Define the Boltzmann collision operator in Lean** — Start with
   hard sphere collision kernel on T³ × R³.

4. **Prove H-theorem in Lean** — This is the entropy inequality that
   NS doesn't have. It's the key additional structure.

5. **Formalize velocity averaging lemma** — The free regularity gain
   from kinetic structure. This is where the extra smoothness comes from.

6. **Attempt the bootstrap** — This is the real mathematical work.
   Start with a priori estimates assuming smooth data, and try to close
   the argument using collision regularization.

---

## References

- DiPerna, R.J., Lions, P.L. (1989). "On the Cauchy problem for
  Boltzmann equations: Global existence and weak stability." Ann. Math.
- Guo, Y. (2003). "The Boltzmann equation in the whole space." Indiana
  Univ. Math. J.
- Golse, F., Saint-Raymond, L. (2004). "The Navier-Stokes limit of the
  Boltzmann equation for bounded collision kernels." Invent. Math.
- Villani, C. (2009). "Hypocoercivity." Mem. Amer. Math. Soc.
- Golse, F., Lions, P.L., Perthame, B., Sentis, R. (1988). "Regularity
  of the moments of the solution of a transport equation." J. Funct. Anal.
- Fefferman, C. (2006). "Existence and smoothness of the Navier-Stokes
  equation." Clay Millennium Problems.
