import FactorialRatio.Definitions
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Coefficient identities

This file records the coefficient identities used by the contiguous and
negative-intercept value formulas.
-/

namespace FactorialRatio

/-- The coefficient of `z^(a*n)` in the normalized E-function `F_{a,b}`. -/
def normalizedCoeff (a b n : ℕ) : ℚ :=
  (b.factorial : ℚ) * n.factorial /
    (((a + 1) * n + b).factorial : ℚ)

/-- Coefficientwise form of the contiguous identity
`F_(a,b-1) = F_(a,b) + (a+1)/(a*b) * θ F_(a,b)`. -/
theorem normalizedCoeff_contiguous (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    normalizedCoeff a (b - 1) n =
      normalizedCoeff a b n +
        ((a + 1 : ℚ) / ((a : ℚ) * b)) * (a * n : ℚ) * normalizedCoeff a b n := by
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hbne : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hpred : b - 1 + 1 = b := by omega
  have hfacb : b.factorial = b * (b - 1).factorial := by
    calc
      b.factorial = (b - 1 + 1).factorial := by rw [hpred]
      _ = (b - 1 + 1) * (b - 1).factorial := Nat.factorial_succ (b - 1)
      _ = b * (b - 1).factorial := by rw [hpred]
  have hindex : (a + 1) * n + b = ((a + 1) * n + (b - 1)) + 1 := by omega
  have hden : ((a + 1) * n + b).factorial =
      ((a + 1) * n + b) * (((a + 1) * n + (b - 1)).factorial) := by
    conv_lhs => rw [hindex, Nat.factorial_succ]
    rw [hindex]
  unfold normalizedCoeff
  rw [hfacb, hden]
  push_cast
  have hden₀ : ((((a + 1) * n + (b - 1)).factorial : ℕ) : ℚ) ≠ 0 := by
    positivity
  field_simp
  ring

/-- The coefficient identity behind the shift from a negative intercept
`b = r-a-1` to the representative `r`. -/
theorem negative_shift_coefficient (a r n : ℕ) (ha : 1 ≤ a) :
    ((n + 1).factorial : ℚ) /
        (((a + 1) * n + r).factorial : ℚ) =
      1 / (r.factorial : ℚ) *
        (normalizedCoeff a r n +
          1 / (a : ℚ) * (a * n : ℚ) * normalizedCoeff a r n) := by
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hrne : (r.factorial : ℚ) ≠ 0 := by positivity
  have hden : ((((a + 1) * n + r).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  unfold normalizedCoeff
  field_simp
  rw [Nat.factorial_succ]
  push_cast
  ring

end FactorialRatio
