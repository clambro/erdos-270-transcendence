import FactorialRatio.Definitions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Field

/-!
# Elementary irrationality

This file contains the unconditional Lean proof that `C_{a,b}` is irrational
for `a ≥ 1` and `0 ≤ b ≤ a`.
-/

namespace FactorialRatio

open Filter Topology

/-- A positive sequence of rational approximants with integer numerators and denominators,
whose denominator-scaled errors tend to zero, cannot converge to a rational number. This is
the abstract arithmetic contradiction used in the paper. -/
theorem irrational_of_integer_approximants {x : ℝ} (D P : ℕ → ℕ)
    (hD : ∀ N, 0 < D N)
    (hpos : ∀ N, 0 < x - (P N : ℝ) / (D N : ℝ))
    (hzero : Tendsto
      (fun N ↦ (D N : ℝ) * (x - (P N : ℝ) / (D N : ℝ)))
      atTop (𝓝 0)) :
    Irrational x := by
  rw [Irrational]
  rintro ⟨r, rfl⟩
  have hrden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hscaled : Tendsto
      (fun N ↦ (r.den : ℝ) *
        ((D N : ℝ) * ((r : ℝ) - (P N : ℝ) / (D N : ℝ))))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hzero
  obtain ⟨N, hN⟩ := (eventually_atTop.1 <| hscaled.eventually (Iio_mem_nhds zero_lt_one))
  have hlt := hN N le_rfl
  let z : ℤ := r.num * (D N : ℤ) - (r.den : ℤ) * (P N : ℤ)
  have hz : (z : ℝ) = (r.den : ℝ) *
      ((D N : ℝ) * ((r : ℝ) - (P N : ℝ) / (D N : ℝ))) := by
    dsimp [z]
    rw [Rat.cast_def]
    push_cast
    field_simp [show (D N : ℝ) ≠ 0 by exact_mod_cast (hD N).ne']
  have hzpos : (0 : ℝ) < z := by
    rw [hz]
    exact mul_pos hrden (mul_pos (by exact_mod_cast hD N) (hpos N))
  have hzpos_int : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzone_int : (1 : ℤ) ≤ z := by omega
  have hzone : (1 : ℝ) ≤ z := by exact_mod_cast hzone_int
  have hzlt : (z : ℝ) < 1 := by simpa only [hz] using hlt
  exact (not_lt_of_ge hzone hzlt)

/-- The integer quotient `D_{n+1}/D_n` after cancelling the factor `n+1`.
The erased index is the factor `(a + 1) * (n + 1)`. -/
def denominatorStep (a b n : ℕ) : ℕ :=
  (a + 1) * ∏ j ∈ (Finset.range (a + 1)).erase (a - b),
    ((a + 1) * n + b + (j + 1))

private theorem cancelled_full_product (a b n : ℕ) (hb : b ≤ a) :
    (n + 1) * denominatorStep a b n =
      (((a + 1) * n + b + 1).ascFactorial (a + 1)) := by
  let f : ℕ → ℕ := fun j ↦ (a + 1) * n + b + (j + 1)
  have hj : a - b ∈ Finset.range (a + 1) := by
    simp only [Finset.mem_range]
    omega
  have hf : f (a - b) = (a + 1) * (n + 1) := by
    dsimp [f]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [Nat.ascFactorial_eq_prod_range]
  change (n + 1) * ((a + 1) * ∏ j ∈ (Finset.range (a + 1)).erase (a - b), f j) =
    ∏ j ∈ Finset.range (a + 1), ((a + 1) * n + b + 1 + j)
  calc
    (n + 1) * ((a + 1) * ∏ j ∈ (Finset.range (a + 1)).erase (a - b), f j) =
        (∏ j ∈ (Finset.range (a + 1)).erase (a - b), f j) * f (a - b) := by
          rw [hf]
          ac_rfl
    _ = ∏ j ∈ Finset.range (a + 1), f j :=
      Finset.prod_erase_mul (Finset.range (a + 1)) f hj
    _ = ∏ j ∈ Finset.range (a + 1), ((a + 1) * n + b + 1 + j) := by
      apply Finset.prod_congr rfl
      intro j _
      dsimp [f]
      omega

theorem denominator_succ (a b n : ℕ) (hb : b ≤ a) :
    denominator a b (n + 1) = denominator a b n * denominatorStep a b n := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (n + 1))
  calc
    (n + 1).factorial * denominator a b (n + 1) =
        ((a + 1) * (n + 1) + b).factorial := factorial_mul_denominator a b (n + 1)
    _ = (((a + 1) * n + b) + (a + 1)).factorial := by
      congr 1
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    _ = ((a + 1) * n + b).factorial *
        (((a + 1) * n + b + 1).ascFactorial (a + 1)) := by
      rw [Nat.factorial_mul_ascFactorial]
    _ = (n.factorial * denominator a b n) *
        ((n + 1) * denominatorStep a b n) := by
      rw [factorial_mul_denominator, cancelled_full_product a b n hb]
    _ = (n + 1).factorial * (denominator a b n * denominatorStep a b n) := by
      rw [Nat.factorial_succ]
      ac_rfl

theorem denominatorStep_pos (a b n : ℕ) : 0 < denominatorStep a b n := by
  unfold denominatorStep
  positivity

theorem denominatorStep_ge_index (a b n : ℕ) (ha : 1 ≤ a) :
    n + 1 ≤ denominatorStep a b n := by
  let j₀ := a - b
  let j := if j₀ = 0 then 1 else 0
  have hj_range : j ∈ Finset.range (a + 1) := by
    simp only [Finset.mem_range]
    dsimp [j, j₀]
    split_ifs <;> omega
  have hj_ne : j ≠ j₀ := by
    dsimp [j]
    split_ifs with h
    · omega
    · exact fun h0 ↦ h h0.symm
  have hj_erase : j ∈ (Finset.range (a + 1)).erase j₀ := by
    simp only [Finset.mem_erase]
    exact ⟨hj_ne, hj_range⟩
  have hfactor : n + 1 ≤ (a + 1) * n + b + (j + 1) := by
    have hn : n ≤ (a + 1) * n := by
      simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ a + 1 by omega)
    omega
  have hprod : (a + 1) * n + b + (j + 1) ≤
      ∏ k ∈ (Finset.range (a + 1)).erase j₀, ((a + 1) * n + b + (k + 1)) := by
    exact Finset.single_le_prod'
      (f := fun k ↦ (a + 1) * n + b + (k + 1)) (fun k _ ↦ by omega) hj_erase
  calc
    n + 1 ≤ (a + 1) * n + b + (j + 1) := hfactor
    _ ≤ ∏ k ∈ (Finset.range (a + 1)).erase j₀,
        ((a + 1) * n + b + (k + 1)) := hprod
    _ ≤ denominatorStep a b n := by
      unfold denominatorStep
      exact Nat.le_mul_of_pos_left _ (by omega)

theorem denominator_dvd_of_le (a b m n : ℕ) (hb : b ≤ a) (h : m ≤ n) :
    denominator a b m ∣ denominator a b n := by
  induction n, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n _ ih =>
      rw [denominator_succ a b n hb]
      exact dvd_mul_of_dvd_left ih _

theorem denominator_mul_pow_le (a b N k : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    denominator a b N * (N + 1) ^ k ≤ denominator a b (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        denominator a b N * (N + 1) ^ (k + 1) =
            (denominator a b N * (N + 1) ^ k) * (N + 1) := by
          rw [pow_succ]
          ac_rfl
        _ ≤ denominator a b (N + k) * (N + 1) := Nat.mul_le_mul_right _ ih
        _ ≤ denominator a b (N + k) * denominatorStep a b (N + k) := by
          apply Nat.mul_le_mul_left
          have hs := denominatorStep_ge_index a b (N + k) ha
          omega
        _ = denominator a b ((N + k) + 1) :=
          (denominator_succ a b (N + k) hb).symm
        _ = denominator a b (N + (k + 1)) := by rw [Nat.add_assoc]

theorem two_le_denominator_one (a b : ℕ) (ha : 1 ≤ a) :
    2 ≤ denominator a b 1 := by
  have hfac := factorial_mul_denominator a b 1
  simp only [Nat.factorial_one, one_mul] at hfac
  rw [hfac]
  have hindex : 2 ≤ (a + 1) * 1 + b := by omega
  simpa using Nat.factorial_le hindex

theorem pow_two_le_denominator (a b n : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    2 ^ (n + 1) ≤ denominator a b (n + 1) := by
  calc
    2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ac_rfl
    _ ≤ denominator a b 1 * 2 ^ n := Nat.mul_le_mul_right _ (two_le_denominator_one a b ha)
    _ ≤ denominator a b (1 + n) := denominator_mul_pow_le a b 1 n ha hb
    _ = denominator a b (n + 1) := by rw [Nat.add_comm]

theorem summand_le_geometric (a b n : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    summand a b (n + 1) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  rw [summand_eq_inv_denominator, div_pow]
  simpa only [one_pow, one_div] using
    one_div_le_one_div_of_le (show (0 : ℝ) < 2 ^ (n + 1) by positivity)
      (show (2 ^ (n + 1) : ℝ) ≤ denominator a b (n + 1) by
        exact_mod_cast pow_two_le_denominator a b n ha hb)

theorem summable_summand (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Summable (fun n : ℕ ↦ summand a b (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n ↦ by
    rw [summand_eq_inv_denominator]
    positivity) (fun n ↦ summand_le_geometric a b n ha hb) ?_
  exact (summable_nat_add_iff 1).2 summable_geometric_two

/-- Increasing the intercept can only increase the reciprocal denominator. -/
theorem denominator_mono_intercept (a b c n : ℕ) (hbc : b ≤ c) :
    denominator a b n ≤ denominator a c n := by
  apply Nat.le_of_mul_le_mul_left (c := n.factorial) _ (Nat.factorial_pos n)
  rw [factorial_mul_denominator, factorial_mul_denominator]
  exact Nat.factorial_le (by omega)

/-- Increasing the intercept can only decrease a term of the series. -/
theorem summand_anti_intercept (a b c n : ℕ) (hbc : b ≤ c) :
    summand a c n ≤ summand a b n := by
  rw [summand_eq_inv_denominator, summand_eq_inv_denominator]
  have hcast : (denominator a b n : ℝ) ≤ denominator a c n := by
    exact_mod_cast denominator_mono_intercept a b c n hbc
  simpa only [one_div] using one_div_le_one_div_of_le
    (show (0 : ℝ) < denominator a b n by exact_mod_cast denominator_pos a b n) hcast

/-- The geometric majorant remains valid for every nonnegative intercept, not only
for the divisibility range `b ≤ a`. -/
theorem summand_le_geometric_all (a b n : ℕ) (ha : 1 ≤ a) :
    summand a b (n + 1) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  exact (summand_anti_intercept a 0 b (n + 1) (Nat.zero_le b)).trans
    (summand_le_geometric a 0 n ha (Nat.zero_le a))

/-- The defining series converges for every nonnegative intercept. -/
theorem summable_summand_all (a b : ℕ) (ha : 1 ≤ a) :
    Summable (fun n : ℕ ↦ summand a b (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n ↦ by
    rw [summand_eq_inv_denominator]
    positivity) (fun n ↦ summand_le_geometric_all a b n ha) ?_
  exact (summable_nat_add_iff 1).2 summable_geometric_two

/-- Numerator obtained by clearing the first `N + 1` terms with `D_{N+1}`. -/
def partialNumerator (a b N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1),
    denominator a b (N + 1) / denominator a b (n + 1)

theorem partial_sum_eq_div (a b N : ℕ) (hb : b ≤ a) :
    (∑ n ∈ Finset.range (N + 1), summand a b (n + 1)) =
      (partialNumerator a b N : ℝ) / denominator a b (N + 1) := by
  rw [partialNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [summand_eq_inv_denominator]
  have hle : n + 1 ≤ N + 1 := by
    simp only [Finset.mem_range] at hn
    omega
  have hdvd := denominator_dvd_of_le a b (n + 1) (N + 1) hb hle
  have hsmall : (denominator a b (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos a b (n + 1)).ne'
  have hlarge : (denominator a b (N + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos a b (N + 1)).ne'
  rw [eq_div_iff hlarge, inv_mul_eq_div, ← Nat.cast_div hdvd hsmall]

/-- The tail following the first `N + 1` terms. -/
noncomputable def seriesTail (a b N : ℕ) : ℝ :=
  ∑' k : ℕ, summand a b (N + 2 + k)

theorem summable_seriesTail (a b N : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Summable (fun k : ℕ ↦ summand a b (N + 2 + k)) := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (summable_nat_add_iff (N + 1)).2 (summable_summand a b ha hb)

theorem scaled_tail_term_le (a b N k : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    (denominator a b (N + 1) : ℝ) * summand a b (N + 2 + k) ≤
      ((1 : ℝ) / (N + 2)) ^ (k + 1) := by
  rw [summand_eq_inv_denominator, div_pow]
  simp only [one_pow]
  rw [← div_eq_mul_inv]
  have hgrowth := denominator_mul_pow_le a b (N + 1) (k + 1) ha hb
  have hbase : N + 1 + 1 = N + 2 := by omega
  rw [hbase] at hgrowth
  have htarget : N + 1 + (k + 1) = N + 2 + k := by omega
  rw [htarget] at hgrowth
  rw [div_le_div_iff₀]
  · norm_num
    exact_mod_cast hgrowth
  · exact_mod_cast denominator_pos a b (N + 2 + k)
  · positivity

theorem scaled_seriesTail_le (a b N : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    (denominator a b (N + 1) : ℝ) * seriesTail a b N ≤ 1 / (N + 1 : ℝ) := by
  have ht := summable_seriesTail a b N ha hb
  have hratio_nonneg : (0 : ℝ) ≤ 1 / (N + 2) := by positivity
  have hratio_lt : (1 : ℝ) / (N + 2) < 1 := by
    rw [div_lt_one]
    · exact_mod_cast (show 1 < N + 2 by omega)
    · positivity
  have hg : Summable (fun k : ℕ ↦ ((1 : ℝ) / (N + 2)) ^ (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hratio_nonneg hratio_lt)
  calc
    (denominator a b (N + 1) : ℝ) * seriesTail a b N =
        ∑' k : ℕ, (denominator a b (N + 1) : ℝ) * summand a b (N + 2 + k) := by
      rw [seriesTail, ht.tsum_mul_left]
    _ ≤ ∑' k : ℕ, ((1 : ℝ) / (N + 2)) ^ (k + 1) :=
      (ht.mul_left _).tsum_le_tsum (fun k ↦ scaled_tail_term_le a b N k ha hb) hg
    _ = 1 / (N + 1 : ℝ) := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hratio_nonneg hratio_lt]
      have hne : (1 : ℝ) + N ≠ 0 := by positivity
      have hne2 : (N : ℝ) + 2 ≠ 0 := by positivity
      calc
        (1 - 1 / (N + 2 : ℝ))⁻¹ * (1 / (N + 2)) =
            ((1 : ℝ) + N)⁻¹ := by
              field_simp [hne2]
              rw [show (N : ℝ) + 2 - 1 = 1 + N by ring]
              exact div_self hne
        _ = 1 / (N + 1 : ℝ) := by rw [one_div]; congr 1; ring

theorem partial_sum_add_seriesTail (a b N : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    (∑ n ∈ Finset.range (N + 1), summand a b (n + 1)) + seriesTail a b N =
      constant a b := by
  simpa only [constant, seriesTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (summable_summand a b ha hb).sum_add_tsum_nat_add (N + 1)

theorem seriesTail_pos (a b N : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    0 < seriesTail a b N := by
  rw [seriesTail]
  exact (summable_seriesTail a b N ha hb).tsum_pos
    (fun k ↦ by
      rw [summand_eq_inv_denominator]
      exact inv_nonneg.mpr (by positivity)) 0
    (by
      rw [summand_eq_inv_denominator]
      exact inv_pos.mpr (by exact_mod_cast denominator_pos a b (N + 2 + 0)))

theorem approximation_error_eq_tail (a b N : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    constant a b - (partialNumerator a b N : ℝ) / denominator a b (N + 1) =
      seriesTail a b N := by
  rw [← partial_sum_eq_div a b N hb]
  rw [← partial_sum_add_seriesTail a b N ha hb]
  ring

theorem scaled_approximation_error_tendsto_zero (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Tendsto
      (fun N ↦ (denominator a b (N + 1) : ℝ) *
        (constant a b - (partialNumerator a b N : ℝ) / denominator a b (N + 1)))
      atTop (𝓝 0) := by
  have hupper : ∀ N : ℕ,
      (denominator a b (N + 1) : ℝ) * seriesTail a b N ≤ 1 / (N + 1 : ℝ) :=
    fun N ↦ scaled_seriesTail_le a b N ha hb
  have hlimit : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqueeze : Tendsto
      (fun N ↦ (denominator a b (N + 1) : ℝ) * seriesTail a b N)
      atTop (𝓝 0) :=
    squeeze_zero
      (fun N ↦ mul_nonneg (by positivity) (seriesTail_pos a b N ha hb).le)
      hupper hlimit
  convert hsqueeze using 1
  funext N
  rw [approximation_error_eq_tail a b N ha hb]

/-- **Elementary irrationality theorem.** For every `a ≥ 1` and `b ≤ a`, the
factorial-ratio series `C_{a,b}` is irrational. Since `b : ℕ`, this is exactly the
paper's range `a ≥ 1`, `0 ≤ b ≤ a`. -/
theorem constant_irrational (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Irrational (constant a b) := by
  apply irrational_of_integer_approximants
    (fun N ↦ denominator a b (N + 1)) (partialNumerator a b)
  · exact fun N ↦ denominator_pos a b (N + 1)
  · intro N
    rw [approximation_error_eq_tail a b N ha hb]
    exact seriesTail_pos a b N ha hb
  · exact scaled_approximation_error_tendsto_zero a b ha hb

end FactorialRatio
