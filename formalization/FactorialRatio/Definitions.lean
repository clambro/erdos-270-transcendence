import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The affine factorial-ratio series

Definitions shared by the formal verification of the elementary and transcendence
arguments.
-/

namespace FactorialRatio

/-- The `n`th term of the affine factorial-ratio series, indexed from `n = 1`. -/
noncomputable def summand (a b n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((((a + 1) * n + b).factorial : ℕ) : ℝ)

/-- The affine factorial-ratio constant `C_{a,b}`, with the paper's indexing. -/
noncomputable def constant (a b : ℕ) : ℝ :=
  ∑' n : ℕ, summand a b (n + 1)

/-- The same summand with an integer intercept. Under the paper's hypothesis
`1 - a ≤ b`, the factorial argument is positive for every `n ≥ 1`; `Int.toNat`
only supplies a total Lean definition outside that range. -/
noncomputable def integerSummand (a : ℕ) (b : ℤ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) /
    ((((((a + 1) * n : ℕ) : ℤ) + b).toNat).factorial : ℝ)

/-- The factorial-ratio constant with the integer intercept used in the paper's
main theorem. -/
noncomputable def integerConstant (a : ℕ) (b : ℤ) : ℝ :=
  ∑' n : ℕ, integerSummand a b (n + 1)

/-- After shifting `n = m + 1`, an integer intercept `b` becomes `a + 1 + b`.
The natural-number value is used when this quantity is nonnegative. -/
def shiftedIntercept (a : ℕ) (b : ℤ) : ℕ :=
  (((a + 1 : ℕ) : ℤ) + b).toNat

/-- In the manuscript's range `b ≥ 1-a`, the `Int.toNat` in `integerSummand`
does not truncate: every factorial argument occurring in the series is at least two. -/
theorem integer_factorial_index_ge_two (a n : ℕ) (b : ℤ)
    (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    2 ≤ (((((a + 1) * (n + 1) : ℕ) : ℤ) + b).toNat) := by
  let t : ℤ := (((a + 1) * (n + 1) : ℕ) : ℤ) + b
  change 2 ≤ t.toNat
  have hprod : 0 ≤ ((a + 1 : ℕ) : ℤ) * (n : ℤ) := mul_nonneg (by positivity) (by positivity)
  have hrewrite :
      t = ((a + 1 : ℕ) : ℤ) * (n : ℤ) + (a : ℤ) + 1 + b := by
    dsimp [t]
    ring
  have htwo : (2 : ℤ) ≤ t := by
    rw [hrewrite]
    omega
  have hcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have : (2 : ℤ) ≤ (t.toNat : ℤ) := by simpa only [hcast] using htwo
  exact_mod_cast this

/-- The integer reciprocal denominator of `summand a b n`. -/
def denominator (a b n : ℕ) : ℕ :=
  (n + 1).ascFactorial (a * n + b)

theorem factorial_mul_denominator (a b n : ℕ) :
    n.factorial * denominator a b n = ((a + 1) * n + b).factorial := by
  rw [denominator, Nat.factorial_mul_ascFactorial]
  congr 1
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem denominator_pos (a b n : ℕ) : 0 < denominator a b n := by
  simpa [denominator] using Nat.ascFactorial_pos n (a * n + b)

theorem summand_eq_inv_denominator (a b n : ℕ) :
    summand a b n = ((denominator a b n : ℕ) : ℝ)⁻¹ := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hD : ((denominator a b n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos a b n).ne'
  have hfact : ((((a + 1) * n + b).factorial : ℕ) : ℝ) =
      (n.factorial : ℝ) * (denominator a b n : ℝ) := by
    norm_cast
    exact (factorial_mul_denominator a b n).symm
  rw [summand, hfact]
  field_simp

end FactorialRatio
