import FactorialRatio.Definitions
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Coefficient identities

This file records the algebraic identities used in the index shift and Euler reduction.
-/

namespace FactorialRatio

/-- The coefficient of `z^(a*n)` in the normalized E-function `F_{a,b}`. -/
def normalizedCoeff (a b n : ℕ) : ℚ :=
  (b.factorial : ℚ) * n.factorial /
    (((a + 1) * n + b).factorial : ℚ)

/-- The coefficient multiplier produced by
`∏_{k=1}^q (θ/a + k)` on a monomial `z^(a*n)`. -/
def eulerMultiplier (q n : ℕ) : ℕ :=
  (n + 1).ascFactorial q

/-- Euclidean division supplies the quotient and representative used in the Euler
reduction, with `0 ≤ r ≤ a`. -/
theorem intercept_division_algorithm (a b : ℕ) :
    b = (b / (a + 1)) * (a + 1) + b % (a + 1) ∧ b % (a + 1) ≤ a := by
  constructor
  · simpa only [Nat.mul_comm] using (Nat.div_add_mod b (a + 1)).symm
  · have hmod := Nat.mod_lt b (show 0 < a + 1 by omega)
    omega

theorem intercept_quotient_pos_of_beyond (a b : ℕ) (hb : a < b) :
    1 ≤ b / (a + 1) := by
  exact Nat.div_pos (by omega) (by omega)

theorem eulerMultiplier_eq_prod (q n : ℕ) :
    eulerMultiplier q n = ∏ k ∈ Finset.range q, (n + (k + 1)) := by
  unfold eulerMultiplier
  rw [Nat.ascFactorial_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k _
  omega

theorem factorial_mul_eulerMultiplier (q n : ℕ) :
    n.factorial * eulerMultiplier q n = (n + q).factorial := by
  exact Nat.factorial_mul_ascFactorial n q

/-- Coefficientwise form of the Euler reduction from an arbitrary nonnegative
intercept `b = q(a+1)+r` to the representative `0 ≤ r ≤ a`. -/
theorem euler_reduction_coefficient (a b q r n : ℕ)
    (hb : b = q * (a + 1) + r) :
    (eulerMultiplier q n : ℚ) * normalizedCoeff a b n =
      (b.factorial : ℚ) / r.factorial * normalizedCoeff a r (n + q) := by
  have hindex : (a + 1) * (n + q) + r = (a + 1) * n + b := by
    simp [hb, Nat.mul_add, Nat.mul_comm]
    omega
  have hfactorial : n.factorial * eulerMultiplier q n = (n + q).factorial :=
    factorial_mul_eulerMultiplier q n
  have hfactorial' : eulerMultiplier q n * n.factorial = (n + q).factorial := by
    simpa [Nat.mul_comm] using hfactorial
  unfold normalizedCoeff
  rw [hindex]
  have hbne : ((((a + 1) * n + b).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hrne : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  exact_mod_cast hfactorial'

/-- After clearing the common factor `(a+1)^(a+1)`, this is the coefficient
multiplier in the inhomogeneous hypergeometric differential equation for `F_{a,b}`. -/
def differentialStepNumerator (a b n : ℕ) : ℕ :=
  ((a + 1) * n + b + 1).ascFactorial (a + 1)

theorem differentialStepNumerator_eq_prod (a b n : ℕ) :
    differentialStepNumerator a b n =
      ∏ j ∈ Finset.range (a + 1), ((a + 1) * n + b + (j + 1)) := by
  unfold differentialStepNumerator
  rw [Nat.ascFactorial_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j _
  omega

/-- Coefficient recurrence for the homogeneous part of equation (12) in the
manuscript. It verifies every positive-degree coefficient of that differential
equation; the remaining degree-zero coefficient is checked separately below. -/
theorem differential_equation_coefficient (a b n : ℕ) :
    (differentialStepNumerator a b n : ℚ) * normalizedCoeff a b (n + 1) =
      (n + 1 : ℚ) * normalizedCoeff a b n := by
  have hfactorial :
      ((a + 1) * n + b).factorial * differentialStepNumerator a b n =
        ((a + 1) * (n + 1) + b).factorial := by
    unfold differentialStepNumerator
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hfactorialQ :
      ((((a + 1) * n + b).factorial : ℕ) : ℚ) * differentialStepNumerator a b n =
        (((a + 1) * (n + 1) + b).factorial : ℕ) := by
    exact_mod_cast hfactorial
  unfold normalizedCoeff
  have hden₀ : ((((a + 1) * n + b).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hden₁ : ((((a + 1) * (n + 1) + b).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  rw [Nat.factorial_succ]
  push_cast
  rw [← hfactorialQ]
  ring

/-- The normalized series has constant coefficient one, giving the inhomogeneous
constant term in equation (12). -/
theorem normalizedCoeff_zero (a b : ℕ) : normalizedCoeff a b 0 = 1 := by
  unfold normalizedCoeff
  norm_num
  positivity

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

/-- The diagonal multiplier of `∏_{k=1}^q (θ/a+k)` on `z^(-a*m)`,
with denominators cleared. -/
def resonanceMultiplier (q m : ℕ) : ℤ :=
  ∏ k ∈ Finset.Icc 1 q, ((k : ℤ) - m)

/-- At the exponent `z^(-a)`, the Euler product is resonant: its diagonal
multiplier vanishes as soon as `q ≥ 1`. -/
theorem resonanceMultiplier_one_eq_zero (q : ℕ) (hq : 1 ≤ q) :
    resonanceMultiplier q 1 = 0 := by
  unfold resonanceMultiplier
  apply Finset.prod_eq_zero (i := 1)
  · simp [hq]
  · norm_num

/-- On the two-dimensional space spanned formally by `z^(-a) log z` and
`z^(-a)`, this is the action of the factor `θ/a+k`. The two coordinates are
the logarithmic and log-free coefficients, respectively. -/
def resonanceFactor (a k : ℕ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (((k : ℚ) - 1) * v.1,
    ((k : ℚ) - 1) * v.2 + v.1 / a)

/-- Successively apply the factors with `k=1,...,q` to `z^(-a) log z`. -/
def resonanceAction (a : ℕ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | q + 1 => resonanceFactor a (q + 1) (resonanceAction a q)

/-- Formal verification of
`∏_{k=1}^q (θ/a+k)(z^(-a) log z) = (q-1)!/a · z^(-a)` for `q ≥ 1`. -/
theorem resonanceAction_succ (a q : ℕ) (_ha : 1 ≤ a) :
    resonanceAction a (q + 1) = (0, (q.factorial : ℚ) / a) := by
  induction q with
  | zero =>
      simp [resonanceAction, resonanceFactor]
  | succ q ih =>
      rw [resonanceAction]
      rw [ih]
      apply Prod.ext
      · simp [resonanceFactor]
      · simp only [resonanceFactor, zero_div, add_zero]
        rw [Nat.factorial_succ]
        push_cast
        ring

/-- The forcing coefficient on the right side of the projected Euler
reduction is nonzero. -/
def resonantForcingCoeff (a b q r : ℕ) : ℚ :=
  -(b.factorial : ℚ) * (q - 1).factorial /
    (((a + 1) * (q - 1) + r).factorial : ℚ)

theorem resonantForcingCoeff_ne_zero (a b q r : ℕ) :
    resonantForcingCoeff a b q r ≠ 0 := by
  unfold resonantForcingCoeff
  apply div_ne_zero
  · exact mul_ne_zero (neg_ne_zero.mpr (by positivity)) (by positivity)
  · positivity

/-- A log-free Laurent coefficient at `z^(-a)` cannot solve the projected Euler
equation: the operator multiplier is zero while the forcing coefficient is nonzero. -/
theorem no_log_free_resonant_coefficient (a b q r : ℕ) (hq : 1 ≤ q) :
    ¬ ∃ c : ℚ,
      (resonanceMultiplier q 1 : ℚ) * c = resonantForcingCoeff a b q r := by
  rintro ⟨c, hc⟩
  have hzero : (resonanceMultiplier q 1 : ℚ) = 0 := by
    rw [resonanceMultiplier_one_eq_zero q hq]
    norm_num
  rw [hzero, zero_mul] at hc
  exact resonantForcingCoeff_ne_zero a b q r hc.symm

/-- The logarithmic coefficient displayed in equation (18) of the manuscript. -/
def forcedLogCoeff (a b q r : ℕ) : ℚ :=
  -(a : ℚ) * b.factorial /
    (((a + 1) * (q - 1) + r).factorial : ℚ)

/-- Multiplying the resonant logarithmic solution by `forcedLogCoeff` produces
exactly the nonzero `z^(-a)` forcing coefficient. -/
theorem forcedLogCoeff_mul_resonanceAction (a b q r : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) :
    forcedLogCoeff a b q r * (resonanceAction a q).2 =
      resonantForcingCoeff a b q r := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rw [resonanceAction_succ a p ha]
  unfold forcedLogCoeff resonantForcingCoeff
  simp only [Nat.succ_sub_one]
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hden : ((((a + 1) * p + r).factorial : ℕ) : ℚ) ≠ 0 := by
    positivity
  field_simp

end FactorialRatio
