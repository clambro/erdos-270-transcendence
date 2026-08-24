import FactorialRatio.ValueIdentities
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# External transcendence inputs

The Salikhov, Salikhov--Viskina, and Beukers theorems are not presently available in
mathlib. Their exact interfaces will be exposed here as hypotheses rather than hidden
behind `axiom` declarations or `sorry`.
-/

namespace FactorialRatio

/-- Linear independence of `1` and `x` with real algebraic coefficients. This is the
real-valued form of linear independence over `Q̄` needed in the fundamental strip. -/
def OneAndValueLinearIndependent (x : ℝ) : Prop :=
  ∀ c₀ c₁ : ℝ,
    IsAlgebraic ℚ c₀ → IsAlgebraic ℚ c₁ →
      c₀ + c₁ * x = 0 → c₀ = 0 ∧ c₁ = 0

/-- Linear independence of `1`, `x`, and `y` with real algebraic coefficients. -/
def OneAndTwoValuesLinearIndependent (x y : ℝ) : Prop :=
  ∀ c₀ c₁ c₂ : ℝ,
    IsAlgebraic ℚ c₀ → IsAlgebraic ℚ c₁ → IsAlgebraic ℚ c₂ →
      c₀ + c₁ * x + c₂ * y = 0 → c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0

/-- Linear independence of two specified real values with algebraic coefficients.
Unlike `OneAndValueLinearIndependent`, this predicate has no constant coordinate. -/
def TwoValuesLinearIndependent (x y : ℝ) : Prop :=
  ∀ c₁ c₂ : ℝ,
    IsAlgebraic ℚ c₁ → IsAlgebraic ℚ c₂ →
      c₁ * x + c₂ * y = 0 → c₁ = 0 ∧ c₂ = 0

/-- The Gaussian integral identity for the base case, separated as an explicit input
until its termwise-integration proof is formalized. Crmarić and Kovač record exactly
this identity in the source cited by the manuscript. -/
structure BaseCaseGaussianIdentity : Prop where
  identity : constant 1 0 = Real.exp (1 / 4 : ℝ) * gaussianHalfIntegral

/-- The precise special-value consequence of Siegel--Shidlovsky used by the
MathOverflow argument at `x=1/4`: `y(1/4)` and `exp(-1/4)` are linearly independent
over the real algebraic numbers. The published argument proves the stronger statement
that these two values are algebraically independent. -/
structure BaseCaseSiegelShidlovskyInput : Prop where
  independent : TwoValuesLinearIndependent gaussianYQuarter expNegQuarter

/-- The precise consequences of the Salikhov and Salikhov--Viskina value theorems used
by the formalized argument. The first field covers `1,F`; the second is required for
the shifted negative-intercept cases and covers `1,F,θF` when `a ≥ 2`.

This structure is an explicit hypothesis. Constructing it from the published papers is
outside mathlib and is not asserted by an `axiom` declaration. -/
structure FundamentalStripInput : Prop where
  pair : ∀ a r : ℕ, 1 ≤ a → r ≤ a →
    OneAndValueLinearIndependent (normalizedValue a r)
  triple : ∀ a r : ℕ, 2 ≤ a → 2 ≤ r → r ≤ a →
    OneAndTwoValuesLinearIndependent (normalizedValue a r) (eulerValue a r)

/-- The specialized value-independence conclusion produced, for `b > a`, by the
paper's functional-minimality argument followed by Beukers's lifting theorem.

As with `FundamentalStripInput`, this is passed explicitly. The formalization checks the
coefficient reduction and resonance arithmetic but does not formalize Levelt--Turrittin
theory, E-functions, or Beukers's theorem. -/
structure BeyondStripInput : Prop where
  pair : ∀ a b : ℕ, 1 ≤ a → a < b →
    OneAndValueLinearIndependent (normalizedValue a b)

/-- The fixed-slope value-independence consequence of the Salikhov,
Salikhov--Viskina, formal-at-infinity, trace-descent, and Beukers arguments.

The family has `a + 1` coordinates: `C_(a,0),...,C_(a,a-1),C_(a,a+1)`.
This interface is passed explicitly because the analytic theorems needed to
construct it are not available in mathlib. -/
structure FixedSlopeAlgebraicIndependenceInput : Prop where
  independent : ∀ a : ℕ, 1 ≤ a → AlgebraicIndependent ℚ (fixedSlopeBasis a)

end FactorialRatio
