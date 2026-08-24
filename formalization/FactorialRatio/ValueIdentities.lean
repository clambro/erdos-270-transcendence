import FactorialRatio.CoefficientIdentities
import FactorialRatio.ElementaryIrrationality
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Identities among the special values

This file passes from the coefficient identities to the convergent real series used in
the article. No transcendence theorem is used here.
-/

namespace FactorialRatio

/-- The normalized value `F_{a,b}(1)`. -/
noncomputable def normalizedValue (a b : ℕ) : ℝ :=
  1 + (b.factorial : ℝ) * constant a b

/-- The Euler derivative `(θ F_{a,b})(1)`, represented by its defining series. -/
noncomputable def eulerValue (a b : ℕ) : ℝ :=
  (b.factorial : ℝ) *
    ∑' n : ℕ, (a * (n + 1) : ℝ) * summand a b (n + 1)

/-- The proposed fixed-slope transcendence basis. The first `a` coordinates are
`C_(a,0),...,C_(a,a-1)` and the final coordinate is the resonant boundary value
`C_(a,a+1)`. -/
noncomputable def fixedSlopeBasis (a : ℕ) (i : Fin (a + 1)) : ℝ :=
  if i.1 < a then constant a i.1 else constant a (a + 1)

theorem fixedSlopeBasis_of_lt (a : ℕ) (i : Fin (a + 1)) (hi : i.1 < a) :
    fixedSlopeBasis a i = constant a i.1 := by
  simp [fixedSlopeBasis, hi]

theorem fixedSlopeBasis_last (a : ℕ) :
    fixedSlopeBasis a (Fin.last a) = constant a (a + 1) := by
  simp [fixedSlopeBasis]

/-- The odd-factorial series occurring after the elementary reindexing of the
base case `C_{1,0}`. -/
noncomputable def oddFactorialSeries : ℝ :=
  ∑' n : ℕ, (n.factorial : ℝ) / ((2 * n + 1).factorial : ℝ)

/-- The Gaussian integral in the representation of `C_{1,0}` recorded by
Crmarić and Kovač. -/
noncomputable def gaussianHalfIntegral : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-t ^ 2)

/-- The special value `y(1/4)=2∫₀^{1/2} exp(-t²)dt` used in the
Siegel--Shidlovsky proof of the base case. -/
noncomputable def gaussianYQuarter : ℝ :=
  2 * gaussianHalfIntegral

/-- The second special value in the base-case Siegel--Shidlovsky argument. -/
noncomputable def expNegQuarter : ℝ :=
  Real.exp (-(1 / 4 : ℝ))

theorem expNegQuarter_ne_zero : expNegQuarter ≠ 0 := by
  exact Real.exp_ne_zero _

theorem intervalIntegrable_gaussianHalf :
    IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t ^ 2)) MeasureTheory.volume
      (0 : ℝ) (1 / 2 : ℝ) := by
  have hinner : Continuous (fun t : ℝ ↦ -t ^ 2) := by fun_prop
  exact (Real.continuous_exp.comp hinner).intervalIntegrable _ _

/-- The termwise identity
`(n+1)!/(2n+2)! = (1/2) n!/(2n+1)!` behind the base-case reindexing. -/
theorem base_summand_reindex (n : ℕ) :
    summand 1 0 (n + 1) =
      (1 / 2 : ℝ) * ((n.factorial : ℝ) / ((2 * n + 1).factorial : ℝ)) := by
  unfold summand
  change ((n + 1).factorial : ℝ) / ((2 * (n + 1)).factorial : ℝ) = _
  have hnum : (n + 1).factorial = (n + 1) * n.factorial := by
    exact Nat.factorial_succ n
  have hden : (2 * (n + 1)).factorial =
      (2 * n + 2) * (2 * n + 1).factorial := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
  rw [hnum, hden]
  push_cast
  have hn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hodd : (((2 * n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The exact series reindexing adjacent to the Gaussian representation:
`C_{1,0} = (1/2) ∑ n!/(2n+1)!`. -/
theorem constant_one_zero_eq_half_oddFactorialSeries :
    constant 1 0 = (1 / 2 : ℝ) * oddFactorialSeries := by
  rw [constant, oddFactorialSeries, ← tsum_mul_left]
  apply tsum_congr
  exact base_summand_reindex

theorem summable_oddFactorialSeries :
    Summable (fun n : ℕ ↦ (n.factorial : ℝ) / ((2 * n + 1).factorial : ℝ)) := by
  have hs := summable_summand_all 1 0 (by norm_num)
  refine (hs.mul_left 2).congr (fun n ↦ ?_)
  rw [base_summand_reindex]
  ring

/-- After shifting a permissible negative intercept, the resulting series has these
terms. If the original intercept is `b = r-a-1`, its constant is `shiftedConstant a r`. -/
noncomputable def shiftedSummand (a r n : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ) /
    (((a + 1) * n + r).factorial : ℝ)

noncomputable def shiftedConstant (a r : ℕ) : ℝ :=
  ∑' n : ℕ, shiftedSummand a r n

theorem integerSummand_eq_summand_of_nonneg (a n : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    integerSummand a b n = summand a b.toNat n := by
  have harg :
      (((((a + 1) * n : ℕ) : ℤ) + b).toNat) = (a + 1) * n + b.toNat := by
    rw [Int.toNat_add (by positivity) hb, Int.toNat_natCast]
  simp only [integerSummand, summand, harg]

/-- For a nonnegative integer intercept, the integer-indexed definition agrees with
the original natural-indexed constant. -/
theorem integerConstant_eq_constant_of_nonneg (a : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    integerConstant a b = constant a b.toNat := by
  unfold integerConstant constant
  apply tsum_congr
  intro n
  exact integerSummand_eq_summand_of_nonneg a (n + 1) b hb

theorem integerSummand_succ_eq_shifted (a n : ℕ) (b : ℤ)
    (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    integerSummand a b (n + 1) = shiftedSummand a (shiftedIntercept a b) n := by
  have hbase : 0 ≤ ((a + 1 : ℕ) : ℤ) + b := by
    push_cast
    omega
  have hrewrite :
      ((((a + 1) * (n + 1) : ℕ) : ℤ) + b) =
        (((a + 1) * n : ℕ) : ℤ) + (((a + 1 : ℕ) : ℤ) + b) := by
    push_cast
    ring
  have harg :
      (((((a + 1) * (n + 1) : ℕ) : ℤ) + b).toNat) =
        (a + 1) * n + shiftedIntercept a b := by
    rw [hrewrite, Int.toNat_add (by positivity) hbase, Int.toNat_natCast]
    rfl
  simp only [integerSummand, shiftedSummand, harg]

/-- Reindexing `n = m + 1` identifies every permissible integer-intercept series
with a shifted nonnegative-intercept series. -/
theorem integerConstant_eq_shifted (a : ℕ) (b : ℤ)
    (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    integerConstant a b = shiftedConstant a (shiftedIntercept a b) := by
  unfold integerConstant shiftedConstant
  apply tsum_congr
  intro n
  exact integerSummand_succ_eq_shifted a n b hb

theorem summable_index_mul_summand (a b : ℕ) (ha : 1 ≤ a) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) * summand a b (n + 1)) := by
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ ↦ (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ (n + 1))
    (fun n ↦ mul_nonneg (by positivity) ?_) (fun n ↦ ?_) ?_
  · rw [summand_eq_inv_denominator]
    positivity
  · exact mul_le_mul_of_nonneg_left (summand_le_geometric_all a b n ha) (by positivity)
  · have hgeom₀ : Summable (fun n : ℕ ↦
        (n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have hgeom := (summable_nat_add_iff 1).2 hgeom₀
    simpa only [pow_one, Nat.cast_add, Nat.cast_one] using hgeom

theorem summable_euler_series (a b : ℕ) (ha : 1 ≤ a) :
    Summable (fun n : ℕ ↦ (a * (n + 1) : ℝ) * summand a b (n + 1)) := by
  refine ((summable_index_mul_summand a b ha).mul_left (a : ℝ)).congr (fun n ↦ ?_)
  ring

theorem summable_all_summand (a b : ℕ) (ha : 1 ≤ a) :
    Summable (summand a b) := by
  apply (summable_nat_add_iff 1).1
  simpa only [Nat.add_comm] using summable_summand_all a b ha

theorem summable_all_euler_terms (a b : ℕ) (ha : 1 ≤ a) :
    Summable (fun n : ℕ ↦ (a * n : ℝ) * summand a b n) := by
  apply (summable_nat_add_iff 1).1
  simpa only [Nat.add_comm, Nat.cast_add, Nat.cast_one] using
    summable_euler_series a b ha

theorem summand_zero (a b : ℕ) :
    summand a b 0 = 1 / (b.factorial : ℝ) := by
  simp [summand]

theorem normalizedValue_eq_tsum (a b : ℕ) (ha : 1 ≤ a) :
    normalizedValue a b =
      (b.factorial : ℝ) * ∑' n : ℕ, summand a b n := by
  have hs := summable_all_summand a b ha
  rw [normalizedValue, hs.tsum_eq_zero_add, summand_zero]
  rw [constant]
  have hbpos : (0 : ℝ) < b.factorial := by positivity
  field_simp

theorem eulerValue_eq_tsum (a b : ℕ) (ha : 1 ≤ a) :
    eulerValue a b =
      (b.factorial : ℝ) *
        ∑' n : ℕ, (a * n : ℝ) * summand a b n := by
  rw [eulerValue]
  congr 1
  have hs := summable_all_euler_terms a b ha
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  apply tsum_congr
  intro n
  congr 2
  push_cast
  ring

/-- The special-value form of the contiguous identity used to replace the first
`a` functions by one function and its first `a - 1` Euler derivatives. -/
theorem normalizedValue_contiguous (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    normalizedValue a (b - 1) =
      normalizedValue a b +
        ((a + 1 : ℝ) / ((a : ℝ) * b)) * eulerValue a b := by
  rw [normalizedValue_eq_tsum a (b - 1) ha, normalizedValue_eq_tsum a b ha,
    eulerValue_eq_tsum a b ha]
  have hs : Summable (fun n : ℕ ↦ (b.factorial : ℝ) * summand a b n) :=
    (summable_all_summand a b ha).mul_left (b.factorial : ℝ)
  have he : Summable (fun n : ℕ ↦
      ((a + 1 : ℝ) / ((a : ℝ) * b)) *
        ((b.factorial : ℝ) * ((a * n : ℝ) * summand a b n))) := by
    exact ((summable_all_euler_terms a b ha).mul_left (b.factorial : ℝ)).mul_left
      ((a + 1 : ℝ) / ((a : ℝ) * b))
  calc
    ((b - 1).factorial : ℝ) * ∑' n : ℕ, summand a (b - 1) n =
        ∑' n : ℕ, ((b - 1).factorial : ℝ) * summand a (b - 1) n := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, ((b.factorial : ℝ) * summand a b n +
        ((a + 1 : ℝ) / ((a : ℝ) * b)) *
          ((b.factorial : ℝ) * ((a * n : ℝ) * summand a b n))) := by
      apply tsum_congr
      intro n
      have hq := normalizedCoeff_contiguous a b n ha hb
      unfold normalizedCoeff at hq
      have hreal := congrArg (fun x : ℚ ↦ (x : ℝ)) hq
      norm_num at hreal
      unfold summand
      convert hreal using 1 <;> ring
    _ = (∑' n : ℕ, (b.factorial : ℝ) * summand a b n) +
        ∑' n : ℕ, ((a + 1 : ℝ) / ((a : ℝ) * b)) *
          ((b.factorial : ℝ) * ((a * n : ℝ) * summand a b n)) := hs.tsum_add he
    _ = (∑' n : ℕ, (b.factorial : ℝ) * summand a b n) +
        ((a + 1 : ℝ) / ((a : ℝ) * b)) *
          ((b.factorial : ℝ) * ∑' n : ℕ, (a * n : ℝ) * summand a b n) := by
      rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
    _ = (b.factorial : ℝ) * ∑' n : ℕ, summand a b n +
        ((a + 1 : ℝ) / ((a : ℝ) * b)) *
          ((b.factorial : ℝ) * ∑' n : ℕ, (a * n : ℝ) * summand a b n) := by
      rw [tsum_mul_left]

/-- Pointwise identity behind the fixed-slope affine recurrence. The first term
on the right advances the summation index while lowering the intercept by
`a + 1`. -/
theorem summand_intercept_recurrence (a b n : ℕ) (hb : a + 1 ≤ b) :
    summand a (b - 1) (n + 1) =
      (a + 1 : ℝ) * summand a (b - a - 1) (n + 2) +
        (b - a - 1 : ℝ) * summand a b (n + 1) := by
  have hlowIndex :
      (a + 1) * (n + 2) + (b - a - 1) = (a + 1) * (n + 1) + b := by
    calc
      (a + 1) * (n + 2) + (b - a - 1) =
          (a + 1) * (n + 1) + ((a + 1) + (b - a - 1)) := by ring
      _ = (a + 1) * (n + 1) + b := by omega
  have hleftIndex :
      (a + 1) * (n + 1) + b = ((a + 1) * (n + 1) + (b - 1)) + 1 := by
    omega
  have hnum : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
    exact Nat.factorial_succ (n + 1)
  have hden : ((a + 1) * (n + 1) + b).factorial =
      ((a + 1) * (n + 1) + b) *
        (((a + 1) * (n + 1) + (b - 1)).factorial) := by
    conv_lhs => rw [hleftIndex, Nat.factorial_succ]
    rw [hleftIndex]
  unfold summand
  rw [hlowIndex, hnum, hden]
  push_cast
  have hfac :
      (((((a + 1) * (n + 1) + (b - 1)).factorial : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp
  ring

/-- Unified value recurrence. Its boundary case `b = a + 1` gives equation
(16) of the manuscript; solving it for `constant a b` when `a + 1 < b`
gives equation (17). -/
theorem constant_intercept_recurrence (a b : ℕ) (ha : 1 ≤ a) (hb : a + 1 ≤ b) :
    constant a (b - 1) =
      (a + 1 : ℝ) * (constant a (b - a - 1) - 1 / (b.factorial : ℝ)) +
        (b - a - 1 : ℝ) * constant a b := by
  have hleft := summable_summand_all a (b - 1) ha
  have hlow := summable_summand_all a (b - a - 1) ha
  have hhigh := summable_summand_all a b ha
  have hlowTail : Summable (fun n : ℕ ↦ summand a (b - a - 1) (n + 2)) := by
    refine (hlow.comp_injective (i := fun n : ℕ ↦ n + 1)
      (fun _ _ h ↦ Nat.add_right_cancel h)).congr (fun n ↦ ?_)
    change summand a (b - a - 1) ((n + 1) + 1) =
      summand a (b - a - 1) (n + 2)
    congr 1
  unfold constant
  calc
    (∑' n : ℕ, summand a (b - 1) (n + 1)) =
        ∑' n : ℕ, ((a + 1 : ℝ) * summand a (b - a - 1) (n + 2) +
          (b - a - 1 : ℝ) * summand a b (n + 1)) := by
      apply tsum_congr
      intro n
      exact summand_intercept_recurrence a b n hb
    _ = (a + 1 : ℝ) * ∑' n : ℕ, summand a (b - a - 1) (n + 2) +
        (b - a - 1 : ℝ) * ∑' n : ℕ, summand a b (n + 1) := by
      rw [(hlowTail.mul_left (a + 1 : ℝ)).tsum_add
        (hhigh.mul_left (b - a - 1 : ℝ)), tsum_mul_left, tsum_mul_left]
    _ = (a + 1 : ℝ) *
          ((∑' n : ℕ, summand a (b - a - 1) (n + 1)) - 1 / (b.factorial : ℝ)) +
        (b - a - 1 : ℝ) * ∑' n : ℕ, summand a b (n + 1) := by
      have hsplit := hlow.tsum_eq_zero_add
      have hfirst : summand a (b - a - 1) 1 = 1 / (b.factorial : ℝ) := by
        unfold summand
        have hindex : (a + 1) * 1 + (b - a - 1) = b := by omega
        rw [hindex]
        norm_num
      rw [hfirst] at hsplit
      rw [hsplit]
      ring

/-- Boundary recurrence `C_(a,a) = (a+1) C_(a,0) - 1/a!`. -/
theorem constant_boundary_eq (a : ℕ) (ha : 1 ≤ a) :
    constant a a = (a + 1 : ℝ) * constant a 0 - 1 / (a.factorial : ℝ) := by
  have h := constant_intercept_recurrence a (a + 1) ha (le_rfl)
  norm_num at h ⊢
  calc
    constant a a = (a + 1 : ℝ) *
        (constant a 0 - (((a + 1).factorial : ℝ))⁻¹) := h
    _ = (a + 1 : ℝ) * constant a 0 - ((a.factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ]
      push_cast
      have ha0 : (a : ℝ) + 1 ≠ 0 := by positivity
      have hfac : (a.factorial : ℝ) ≠ 0 := by positivity
      field_simp

/-- Solved form of the fixed-slope recurrence for intercepts beyond `a + 1`. -/
theorem constant_beyond_recurrence (a b : ℕ) (ha : 1 ≤ a) (hb : a + 1 < b) :
    constant a b =
      (constant a (b - 1) - (a + 1 : ℝ) * constant a (b - a - 1) +
        (a + 1 : ℝ) / (b.factorial : ℝ)) / ((b : ℝ) - a - 1) := by
  have h := constant_intercept_recurrence a b ha (Nat.le_of_lt hb)
  have hbR : (a : ℝ) + 1 < b := by exact_mod_cast hb
  have hden : (b : ℝ) - a - 1 ≠ 0 := by linarith
  have hfac : (b.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hden, hfac] at h ⊢
  linarith

theorem shiftedSummand_eq (a r n : ℕ) (ha : 1 ≤ a) :
    shiftedSummand a r n =
      1 / (r.factorial : ℝ) *
        ((r.factorial : ℝ) * summand a r n +
          1 / (a : ℝ) * (a * n : ℝ) *
            ((r.factorial : ℝ) * summand a r n)) := by
  have hq := negative_shift_coefficient a r n ha
  unfold shiftedSummand summand normalizedCoeff at *
  have hreal := congrArg (fun x : ℚ ↦ (x : ℝ)) hq
  norm_num at hreal
  convert hreal using 1
  all_goals ring

theorem summable_shiftedSummand (a r : ℕ) (ha : 1 ≤ a) :
    Summable (shiftedSummand a r) := by
  have hs := (summable_all_summand a r ha).mul_left (r.factorial : ℝ)
  have he := (summable_all_euler_terms a r ha).mul_left (r.factorial : ℝ)
  have he' := he.mul_left (1 / (a : ℝ))
  have hadd := hs.add he'
  have hall := hadd.mul_left (1 / (r.factorial : ℝ))
  refine hall.congr (fun n ↦ ?_)
  rw [shiftedSummand_eq a r n ha]
  ring

/-- The integer-intercept series converges throughout the paper's full range
`a ≥ 1`, `b ≥ 1 - a`. -/
theorem summable_integerSummand (a : ℕ) (b : ℤ) (ha : 1 ≤ a)
    (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    Summable (fun n : ℕ ↦ integerSummand a b (n + 1)) := by
  refine (summable_shiftedSummand a (shiftedIntercept a b) ha).congr (fun n ↦ ?_)
  exact (integerSummand_succ_eq_shifted a n b hb).symm

/-- The exact shifted-value identity used for the negative-intercept cases. -/
theorem shiftedConstant_eq (a r : ℕ) (ha : 1 ≤ a) :
    shiftedConstant a r =
      1 / (r.factorial : ℝ) *
        (normalizedValue a r + 1 / (a : ℝ) * eulerValue a r) := by
  rw [shiftedConstant]
  simp_rw [shiftedSummand_eq a r _ ha]
  rw [tsum_mul_left]
  have hs := (summable_all_summand a r ha).mul_left (r.factorial : ℝ)
  have he := (summable_all_euler_terms a r ha).mul_left (r.factorial : ℝ)
  have he' := he.mul_left (1 / (a : ℝ))
  have he'' : Summable (fun n : ℕ ↦
      1 / (a : ℝ) * (a * n : ℝ) * ((r.factorial : ℝ) * summand a r n)) := by
    refine he'.congr (fun n ↦ ?_)
    ring
  rw [hs.tsum_add he'']
  rw [normalizedValue_eq_tsum a r ha, eulerValue_eq_tsum a r ha]
  have htsum :
      (∑' n : ℕ, 1 / (a : ℝ) * (a * n : ℝ) *
        ((r.factorial : ℝ) * summand a r n)) =
        1 / (a : ℝ) * (r.factorial : ℝ) *
          ∑' n : ℕ, (a * n : ℝ) * summand a r n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  rw [htsum, tsum_mul_left]
  ring

/-- Affine form of the negative-intercept shift, corresponding to equation (18)
of the manuscript after `r = a + 1 + b`. -/
theorem shiftedConstant_affine (a r : ℕ) (ha : 1 ≤ a) (hr : 1 ≤ r) :
    shiftedConstant a r =
      1 / (r.factorial : ℝ) +
        (a + 1 - r : ℝ) / (a + 1 : ℝ) * constant a r +
        1 / (a + 1 : ℝ) * constant a (r - 1) := by
  rw [shiftedConstant_eq a r ha]
  have hc := normalizedValue_contiguous a r ha hr
  unfold normalizedValue at hc ⊢
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hap0 : (a : ℝ) + 1 ≠ 0 := by positivity
  have hrfac0 : (r.factorial : ℝ) ≠ 0 := by positivity
  have hrpred : r - 1 + 1 = r := by omega
  have hrfac : (r.factorial : ℝ) =
      (r : ℝ) * ((r - 1).factorial : ℝ) := by
    norm_cast
    calc
      r.factorial = (r - 1 + 1).factorial := by rw [hrpred]
      _ = (r - 1 + 1) * (r - 1).factorial := Nat.factorial_succ (r - 1)
      _ = r * (r - 1).factorial := by rw [hrpred]
  field_simp [ha0, hr0, hap0, hrfac0] at hc ⊢
  rw [hrfac] at hc ⊢
  linear_combination -hc

end FactorialRatio
