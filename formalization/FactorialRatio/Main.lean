import FactorialRatio.Definitions
import FactorialRatio.ElementaryIrrationality
import FactorialRatio.CoefficientIdentities
import FactorialRatio.ValueIdentities
import FactorialRatio.ExternalTheorems

/-!
# Main results

This file assembles the unconditional elementary theorem and the conditional
transcendence theorem.
-/

namespace FactorialRatio

theorem transcendental_of_oneAndValueLinearIndependent {x : ℝ}
    (h : OneAndValueLinearIndependent x) : Transcendental ℚ x := by
  intro hx
  have hneg : IsAlgebraic ℚ (-x) := hx.neg
  have hone : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  obtain ⟨_, hfalse⟩ := h (-x) 1 hneg hone (by ring)
  norm_num at hfalse

/-- The affine normalization `F_{a,b}(1)=1+b!C_{a,b}` preserves
transcendence in the direction required by the paper. -/
theorem constant_transcendental_of_normalizedValue (a b : ℕ)
    (hF : Transcendental ℚ (normalizedValue a b)) :
    Transcendental ℚ (constant a b) := by
  intro hC
  apply hF
  rw [normalizedValue]
  have hbAlg : IsAlgebraic ℚ (b.factorial : ℝ) := isAlgebraic_natCast b.factorial
  exact IsAlgebraic.add isAlgebraic_one (IsAlgebraic.mul hbAlg hC)

/-- Assuming the cited fundamental-strip value theorem, the constants with
`0 ≤ b ≤ a` are transcendental. -/
theorem fundamental_constant_transcendental
    (published : FundamentalStripInput) (a r : ℕ) (ha : 1 ≤ a) (hr : r ≤ a) :
    Transcendental ℚ (constant a r) := by
  apply constant_transcendental_of_normalizedValue
  exact transcendental_of_oneAndValueLinearIndependent (published.pair a r ha hr)

/-- Conditional on the three-value consequence of the cited theorem, the shifted
constant corresponding to the negative intercept `b=r-a-1` is transcendental. -/
theorem shifted_constant_transcendental
    (published : FundamentalStripInput) (a r : ℕ)
    (ha : 2 ≤ a) (hr₂ : 2 ≤ r) (hr : r ≤ a) :
    Transcendental ℚ (shiftedConstant a r) := by
  intro hshift
  have ha₁ : 1 ≤ a := by omega
  have hfactorial : IsAlgebraic ℚ ((r.factorial : ℝ) * shiftedConstant a r) :=
    (isAlgebraic_natCast r.factorial).mul hshift
  have hc₀ : IsAlgebraic ℚ (-((r.factorial : ℝ) * shiftedConstant a r)) :=
    hfactorial.neg
  have hc₁ : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have hc₂ : IsAlgebraic ℚ (1 / (a : ℝ)) := by
    have haAlg : IsAlgebraic ℚ (a : ℝ) := isAlgebraic_natCast a
    simpa only [one_div] using haAlg.inv
  have hrelation :
      -((r.factorial : ℝ) * shiftedConstant a r) +
          normalizedValue a r + 1 / (a : ℝ) * eulerValue a r = 0 := by
    rw [shiftedConstant_eq a r ha₁]
    have hrne : (r.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  obtain ⟨_, hfalse, _⟩ :=
    published.triple a r ha hr₂ hr
      (-((r.factorial : ℝ) * shiftedConstant a r)) 1 (1 / (a : ℝ))
      hc₀ hc₁ hc₂ (by simpa only [one_mul] using hrelation)
  norm_num at hfalse

/-- Conditional on the two stated literature interfaces, every nonnegative-intercept
constant is transcendental. The proof performs the complete case split and the affine
normalization inside Lean. -/
theorem nonnegative_constant_transcendental
    (fundamental : FundamentalStripInput) (beyond : BeyondStripInput)
    (a b : ℕ) (ha : 1 ≤ a) :
    Transcendental ℚ (constant a b) := by
  by_cases hb : b ≤ a
  · exact fundamental_constant_transcendental fundamental a b ha hb
  · apply constant_transcendental_of_normalizedValue
    exact transcendental_of_oneAndValueLinearIndependent (beyond.pair a b ha (by omega))

/-- **Conditional main theorem.** Given the two explicit external value-independence
interfaces, the factorial-ratio constant is transcendental for every integer intercept
in the paper's full range `a ≥ 1`, `b ≥ 1 - a`. -/
theorem integer_constant_transcendental
    (fundamental : FundamentalStripInput) (beyond : BeyondStripInput)
    (a : ℕ) (b : ℤ) (ha : 1 ≤ a) (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    Transcendental ℚ (integerConstant a b) := by
  by_cases hb₀ : 0 ≤ b
  · rw [integerConstant_eq_constant_of_nonneg a b hb₀]
    exact nonnegative_constant_transcendental fundamental beyond a b.toNat ha
  · have hbneg : b < 0 := lt_of_not_ge hb₀
    rw [integerConstant_eq_shifted a b hb]
    have hbase : 0 ≤ ((a + 1 : ℕ) : ℤ) + b := by
      push_cast
      omega
    have hr_cast : ((shiftedIntercept a b : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) + b := by
      exact Int.toNat_of_nonneg hbase
    have ha₂ : 2 ≤ a := by omega
    have hr₂ : 2 ≤ shiftedIntercept a b := by omega
    have hr : shiftedIntercept a b ≤ a := by omega
    exact shifted_constant_transcendental fundamental a (shiftedIntercept a b) ha₂ hr₂ hr

/-- The unconditional part of the formalization, restated at the main entry point. -/
theorem elementary_constant_irrational (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Irrational (constant a b) :=
  constant_irrational a b ha hb

end FactorialRatio
