import FactorialRatio.ValueIdentities
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# External transcendence inputs

The Salikhov, Salikhov--Viskina, and Beukers theorems are not available in
mathlib. Their exact interfaces will be exposed here as hypotheses rather than hidden
behind `axiom` declarations or `sorry`.
-/

namespace FactorialRatio

/-- Linear independence of two specified real values with algebraic coefficients.
This is the special-value consequence used by the Gaussian base-case proof. -/
def TwoValuesLinearIndependent (x y : ℝ) : Prop :=
  ∀ c₁ c₂ : ℝ,
    IsAlgebraic ℚ c₁ → IsAlgebraic ℚ c₂ →
      c₁ * x + c₂ * y = 0 → c₁ = 0 ∧ c₂ = 0

/-- The Gaussian integral identity for the base case, separated as an explicit input
until its termwise-integration proof is formalized. Crmarić and Kovač record
this identity in the source cited by the manuscript. -/
structure BaseCaseGaussianIdentity : Prop where
  identity : constant 1 0 = Real.exp (1 / 4 : ℝ) * gaussianHalfIntegral

/-- The precise special-value consequence of Siegel--Shidlovsky used by the
MathOverflow argument at `x=1/4`: `y(1/4)` and `exp(-1/4)` are linearly independent
over the real algebraic numbers. The published argument proves the stronger statement
that these two values are algebraically independent. -/
structure BaseCaseSiegelShidlovskyInput : Prop where
  independent : TwoValuesLinearIndependent gaussianYQuarter expNegQuarter

/-- The fixed-slope value-independence consequence of the Salikhov,
Salikhov--Viskina, formal-at-infinity, trace-descent, and Beukers arguments.

The family has `a + 1` coordinates: `C_(a,0),...,C_(a,a-1),C_(a,a+1)`.
This interface is passed explicitly because the analytic theorems needed to
construct it are not available in mathlib. -/
structure FixedSlopeAlgebraicIndependenceInput : Prop where
  independent : ∀ a : ℕ, 1 ≤ a → AlgebraicIndependent ℚ (fixedSlopeBasis a)

end FactorialRatio
