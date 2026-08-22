import FactorialRatio.ExternalTheorems

/-!
# The Gaussian proof of the base-case transcendence statement

This file formalizes the complete deduction from the two inputs cited in Section 3 of
the manuscript: the Gaussian integral identity and the Siegel--Shidlovsky independence
statement at `x=1/4`. The inputs themselves remain explicit because the required
termwise-integration argument and Siegel--Shidlovsky theorem are not in mathlib.
-/

namespace FactorialRatio

/-- The Gaussian identity implies the exact linear relation used in the
transcendence argument:
`y(1/4) = 2 C_{1,0} exp(-1/4)`. -/
theorem gaussianYQuarter_eq_two_mul_constant_mul_expNegQuarter
    (gaussian : BaseCaseGaussianIdentity) :
    gaussianYQuarter = 2 * constant 1 0 * expNegQuarter := by
  rw [gaussianYQuarter, gaussian.identity]
  unfold expNegQuarter
  rw [Real.exp_neg]
  have hexp : Real.exp (1 / 4 : ℝ) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- The final algebraic deduction in the Gaussian proof. If `C_{1,0}` were
algebraic, the preceding identity would give a nontrivial algebraic linear relation
between `y(1/4)` and `exp(-1/4)`. -/
theorem constant_one_zero_transcendental_of_gaussian
    (gaussian : BaseCaseGaussianIdentity)
    (siegelShidlovsky : BaseCaseSiegelShidlovskyInput) :
    Transcendental ℚ (constant 1 0) := by
  intro hC
  have hcoeff : IsAlgebraic ℚ (-2 * constant 1 0) := by
    exact (isAlgebraic_natCast 2).neg.mul hC
  have hrelation :
      (1 : ℝ) * gaussianYQuarter +
          (-2 * constant 1 0) * expNegQuarter = 0 := by
    rw [gaussianYQuarter_eq_two_mul_constant_mul_expNegQuarter gaussian]
    ring
  obtain ⟨hone, _⟩ :=
    siegelShidlovsky.independent 1 (-2 * constant 1 0)
      isAlgebraic_one hcoeff hrelation
  norm_num at hone

end FactorialRatio
