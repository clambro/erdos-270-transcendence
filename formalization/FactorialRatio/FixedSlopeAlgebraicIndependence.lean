import FactorialRatio.ExternalTheorems
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Fixed-slope algebraic independence

This file records the exact value-level boundary of the formalization. The analytic
Salikhov, Viskina--Salikhov, Levelt--Turrittin, trace-descent, and Beukers arguments
are supplied through `FixedSlopeAlgebraicIndependenceInput`. Lean verifies the
algebraic consequences of that input and exposes the extension from rational to
real algebraic coefficients.
-/

namespace FactorialRatio

abbrev RealAlgebraic : Type := algebraicClosure ℚ ℝ

/-- Augment a real-valued family by a distinguished constant coordinate `1`. -/
def withOne {ι : Type*} (x : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => x i

private noncomputable def affineExponent {ι : Type*} [DecidableEq ι] : Option ι → ι →₀ ℕ
  | none => 0
  | some i => Finsupp.single i 1

private theorem affineExponent_injective {ι : Type*} [DecidableEq ι] :
    Function.Injective (affineExponent : Option ι → ι →₀ ℕ) := by
  intro o p h
  cases o with
  | none =>
      cases p with
      | none => rfl
      | some j =>
          have hj := DFunLike.congr_fun h j
          simp [affineExponent] at hj
  | some i =>
      cases p with
      | none =>
          have hi := DFunLike.congr_fun h i
          simp [affineExponent] at hi
      | some j =>
          congr 1
          exact (Finsupp.single_left_injective one_ne_zero) h

private theorem algebraicIndependent_withOne_linearIndependent
    {K ι : Type*} [Field K] [Algebra K ℝ] [DecidableEq ι]
    {x : ι → ℝ} (hx : AlgebraicIndependent K x) :
    LinearIndependent K (withOne x) := by
  have hmonomial :=
    (MvPolynomial.basisMonomials ι K).linearIndependent.comp
      (affineExponent : Option ι → ι →₀ ℕ) affineExponent_injective
  have hmap := hmonomial.map' (MvPolynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr hx)
  have hmap' :
      LinearIndependent K
        (fun o : Option ι ↦
          (affineExponent o).prod fun i k ↦ x i ^ k) := by
    simpa [Function.comp_def, MvPolynomial.coe_basisMonomials,
      MvPolynomial.aeval_monomial] using hmap
  have heval :
      (fun o : Option ι ↦ (affineExponent o).prod fun i k ↦ x i ^ k) =
        withOne x := by
    funext o
    cases o <;> simp [affineExponent, withOne, Finsupp.prod_single_index]
  rwa [heval] at hmap'

private theorem linearIndependent_update_of_eq
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] {v : ι → V}
    (hv : LinearIndependent K v) (i : ι) (y : V) (c : ι → K)
    (hci : c i ≠ 0) (hy : y = ∑ j, c j • v j) :
    LinearIndependent K (Function.update v i y) := by
  apply hv.update i y
  refine ⟨1, mem_nonZeroDivisors_iff_ne_zero.mpr one_ne_zero,
    Finsupp.equivFunOnFinite.symm c, ?_, ?_⟩
  · change c i ∈ nonZeroDivisors K
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hci
  · simp only [one_smul]
    rw [hy]
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]

/-- The consecutive block of `a + 1` values beginning at intercept `s`. -/
noncomputable def fixedSlopeBlock (a s : ℕ) (i : Fin (a + 1)) : ℝ :=
  constant a (s + i)

private theorem member_transcendental_of_withOne_linearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → ℝ}
    (hv : LinearIndependent RealAlgebraic (withOne v)) (i : ι) :
    Transcendental ℚ (v i) := by
  intro hi
  let vi : RealAlgebraic := ⟨v i, mem_algebraicClosure_iff.mpr hi⟩
  let c : Option ι → RealAlgebraic
    | none => -vi
    | some j => if j = i then 1 else 0
  have hc : ∑ j, c j • withOne v j = 0 := by
    simp only [Fintype.sum_option, c, withOne, vi, neg_smul]
    rw [Finset.sum_eq_single i]
    · simp [IntermediateField.smul_def, smul_eq_mul]
    · intro j _ hji
      simp [hji]
    · simp
  have hzero := (Fintype.linearIndependent_iff.mp hv c hc) (some i)
  simp [c] at hzero

private theorem affineCombination_transcendental
    {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → ℝ}
    (hv : LinearIndependent RealAlgebraic (withOne v))
    (y : ℝ) (c₀ : RealAlgebraic) (c : ι → RealAlgebraic)
    (hc : ∃ i, c i ≠ 0)
    (hy : y = c₀ • (1 : ℝ) + ∑ i, c i • v i) :
    Transcendental ℚ y := by
  intro halg
  let ya : RealAlgebraic := ⟨y, mem_algebraicClosure_iff.mpr halg⟩
  let d : Option ι → RealAlgebraic
    | none => c₀ - ya
    | some i => c i
  have hd : ∑ i, d i • withOne v i = 0 := by
    rw [Fintype.sum_option]
    simp only [d, withOne, sub_smul]
    calc
      c₀ • (1 : ℝ) - ya • (1 : ℝ) + ∑ i, c i • v i =
          (c₀ • (1 : ℝ) + ∑ i, c i • v i) - ya • (1 : ℝ) := by abel
      _ = y - ya • (1 : ℝ) := by rw [← hy]
      _ = 0 := by simp [ya, IntermediateField.smul_def, smul_eq_mul]
  have hzero := Fintype.linearIndependent_iff.mp hv d hd
  obtain ⟨i, hi⟩ := hc
  exact hi (by simpa [d] using hzero (some i))

private theorem fixedSlopeBlock_one_linearIndependent
    (published : FixedSlopeAlgebraicIndependenceInput) (a : ℕ) (ha : 1 ≤ a) :
    LinearIndependent RealAlgebraic (withOne (fixedSlopeBlock a 1)) := by
  have hbasis : LinearIndependent RealAlgebraic (withOne (fixedSlopeBasis a)) :=
    algebraicIndependent_withOne_linearIndependent
      ((published.independent a ha).algebraicClosure)
  let zero : Fin (a + 1) := ⟨0, by omega⟩
  let pivot : Option (Fin (a + 1)) := some zero
  let coeff : Option (Fin (a + 1)) → RealAlgebraic
    | none => -(1 / (a.factorial : ℚ))
    | some i => if i = zero then (a + 1 : ℚ) else 0
  have hpivot : coeff pivot ≠ 0 := by
    simp only [coeff, pivot, zero, if_pos]
    exact (map_ne_zero (algebraMap ℚ RealAlgebraic)).mpr (by positivity)
  have hboundary :
      constant a a = ∑ j, coeff j • withOne (fixedSlopeBasis a) j := by
    rw [constant_boundary_eq a ha]
    rw [Fintype.sum_option]
    have hsum :
        ∑ i, coeff (some i) • fixedSlopeBasis a i =
          coeff (some zero) • fixedSlopeBasis a zero := by
      apply Finset.sum_eq_single zero
      · intro i _ hi
        simp [coeff, hi]
      · simp
    simp only [withOne]
    rw [hsum]
    have ha0 : 0 < a := by omega
    simp [coeff, zero, IntermediateField.smul_def, smul_eq_mul,
      fixedSlopeBasis, ha0]
    ring
  have hupdated := linearIndependent_update_of_eq hbasis pivot (constant a a)
    coeff hpivot hboundary
  let p : Equiv.Perm (Fin (a + 1)) :=
    Fin.cycleRange ⟨a - 1, by omega⟩
  have hpermuted := hupdated.comp (Equiv.optionCongr p) (Equiv.optionCongr p).injective
  have hfamily :
      withOne (fixedSlopeBlock a 1) =
        Function.update (withOne (fixedSlopeBasis a)) pivot (constant a a) ∘
          Equiv.optionCongr p := by
    funext j
    cases j with
    | none => rfl
    | some i =>
      simp only [Equiv.optionCongr_apply, Option.map_some, Function.comp_apply]
      by_cases hi : i.1 < a - 1
      · have hip : p i = i + 1 := Fin.cycleRange_of_lt (i := i) (j := ⟨a - 1, by omega⟩)
          (by exact_mod_cast hi)
        have hilast : i < Fin.last a := by
          exact_mod_cast (show i.1 < a by omega)
        have hval : ((i + 1 : Fin (a + 1)) : ℕ) = i.1 + 1 :=
          Fin.val_add_one_of_lt hilast
        have hne : (i + 1 : Fin (a + 1)) ≠ zero := by
          intro h
          have := congrArg Fin.val h
          simp [hval, zero] at this
        rw [hip]
        have hlt : i.1 + 1 < a := by omega
        simp [withOne, fixedSlopeBlock, Function.update, pivot, hne,
          fixedSlopeBasis, hval, hlt, Nat.add_comm]
      · by_cases hieq : i.1 = a - 1
        · have hiFin : i = ⟨a - 1, by omega⟩ := Fin.ext hieq
          have hip : p i = 0 := by
            rw [hiFin]
            exact Fin.cycleRange_self ⟨a - 1, by omega⟩
          rw [hip]
          simp [withOne, fixedSlopeBlock, Function.update, pivot, zero]
          congr 1
          omega
        · have higt : a - 1 < i.1 := by omega
          have hip : p i = i := Fin.cycleRange_of_gt (i := ⟨a - 1, by omega⟩) (j := i)
            (by exact_mod_cast higt)
          rw [hip]
          have hilast : i.1 = a := by omega
          have hne : i ≠ zero := by
            intro h
            have := congrArg Fin.val h
            simp [hilast, zero] at this
            omega
          simp [withOne, fixedSlopeBlock, Function.update, pivot, hne,
            fixedSlopeBasis, hilast]
          congr 1
          omega
  rw [hfamily]
  exact hpermuted

private theorem fixedSlopeBlock_succ_linearIndependent
    (a s : ℕ) (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hblock : LinearIndependent RealAlgebraic (withOne (fixedSlopeBlock a s))) :
    LinearIndependent RealAlgebraic (withOne (fixedSlopeBlock a (s + 1))) := by
  let zero : Fin (a + 1) := ⟨0, by omega⟩
  let pivot : Option (Fin (a + 1)) := some zero
  let b := s + a + 1
  let coeff : Option (Fin (a + 1)) → RealAlgebraic
    | none => (a + 1 : ℚ) / (b.factorial : ℚ) / (s : ℚ)
    | some i =>
        if i = zero then -((a + 1 : ℚ) / (s : ℚ))
        else if i.1 = a then 1 / (s : ℚ)
        else 0
  have hpivot : coeff pivot ≠ 0 := by
    simp only [coeff, pivot, zero, if_pos, neg_ne_zero]
    apply div_ne_zero
    · exact (map_ne_zero (algebraMap ℚ RealAlgebraic)).mpr (by positivity)
    · exact (map_ne_zero (algebraMap ℚ RealAlgebraic)).mpr (by positivity)
  have hb : a + 1 < b := by omega
  have hnext :
      constant a b = ∑ j, coeff j • withOne (fixedSlopeBlock a s) j := by
    have hlast : ∀ i : Fin (a + 1), i.1 = a ↔ i = Fin.last a := by
      intro i
      constructor
      · intro hi
        apply Fin.ext
        simpa using hi
      · rintro rfl
        simp
    have hzeroLast : zero ≠ Fin.last a := by
      intro h
      have := congrArg Fin.val h
      simp [zero] at this
      omega
    rw [constant_beyond_recurrence a b ha hb]
    have hprev : b - 1 = s + a := by omega
    have hlow : b - a - 1 = s := by omega
    rw [hprev, hlow]
    rw [Fintype.sum_option]
    have hsum :
        ∑ i, coeff (some i) • fixedSlopeBlock a s i =
          coeff (some (Fin.last a)) • fixedSlopeBlock a s (Fin.last a) +
            coeff (some zero) • fixedSlopeBlock a s zero := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero)]
      congr 1
      apply Finset.sum_eq_single (Fin.last a)
      · intro i hi hne
        have hizero : i ≠ zero := (Finset.mem_erase.mp hi).1
        have hilast : i.1 ≠ a := by
          intro hia
          exact hne ((hlast i).mp hia)
        simp [coeff, hizero, hilast]
      · intro hnot
        exact (hnot (Finset.mem_erase.mpr ⟨hzeroLast.symm, Finset.mem_univ _⟩)).elim
    simp only [withOne]
    rw [hsum]
    have ha0 : a ≠ 0 := by omega
    simp [coeff, fixedSlopeBlock, zero, b, hlast,
      IntermediateField.smul_def, smul_eq_mul, ha0]
    simp [div_eq_mul_inv]
    ring
  have hupdated := linearIndependent_update_of_eq hblock pivot (constant a b)
    coeff hpivot hnext
  let p : Equiv.Perm (Fin (a + 1)) := finRotate (a + 1)
  have hpermuted := hupdated.comp (Equiv.optionCongr p) (Equiv.optionCongr p).injective
  have hfamily :
      withOne (fixedSlopeBlock a (s + 1)) =
        Function.update (withOne (fixedSlopeBlock a s)) pivot (constant a b) ∘
          Equiv.optionCongr p := by
    funext j
    cases j with
    | none => rfl
    | some i =>
      simp only [Equiv.optionCongr_apply, Option.map_some, Function.comp_apply]
      by_cases hi : i = Fin.last a
      · rw [hi]
        have hp : p (Fin.last a) = zero := by simp [p, zero]
        rw [hp]
        simp [withOne, fixedSlopeBlock, Function.update, pivot, zero, Fin.val_last]
        congr 1
        omega
      · have hval : (p i : ℕ) = i.1 + 1 := by
          simpa [p] using coe_finRotate_of_ne_last hi
        have hne : p i ≠ zero := by
          intro h
          have := congrArg Fin.val h
          simp [hval, zero] at this
        simp [withOne, fixedSlopeBlock, Function.update, pivot, hne, hval]
        congr 1
        omega
  rw [hfamily]
  exact hpermuted

/-- Every consecutive block of `a + 1` positive-intercept values, augmented by
`1`, is linearly independent over the real algebraic numbers. The proof starts
from the algebraically independent fixed-slope basis and propagates the result
through the affine recurrence. -/
theorem fixedSlopeBlock_linearIndependent
    (published : FixedSlopeAlgebraicIndependenceInput) (a s : ℕ)
    (ha : 1 ≤ a) (hs : 1 ≤ s) :
    LinearIndependent RealAlgebraic (withOne (fixedSlopeBlock a s)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction k with
  | zero =>
      simpa using fixedSlopeBlock_one_linearIndependent published a ha
  | succ k ih =>
      have hs' : 1 ≤ 1 + k := by omega
      simpa [Nat.add_assoc] using
        fixedSlopeBlock_succ_linearIndependent a (1 + k) ha hs' ih

/-- Every constant with a nonnegative intercept is transcendental, conditional
only on the fixed-slope algebraic-independence input used by the manuscript. -/
theorem nonnegative_constant_transcendental_of_fixedSlope
    (published : FixedSlopeAlgebraicIndependenceInput)
    (a b : ℕ) (ha : 1 ≤ a) :
    Transcendental ℚ (constant a b) := by
  by_cases hb : b = 0
  · subst hb
    let zero : Fin (a + 1) := ⟨0, by omega⟩
    have h := (published.independent a ha).transcendental zero
    have ha0 : 0 < a := by omega
    simpa [zero, fixedSlopeBasis, ha0] using h
  · have hbpos : 1 ≤ b := by omega
    let zero : Fin (a + 1) := ⟨0, by omega⟩
    have hblock := fixedSlopeBlock_linearIndependent published a b ha hbpos
    have h := member_transcendental_of_withOne_linearIndependent hblock zero
    simpa [zero, fixedSlopeBlock] using h

/-- The shifted value representing a permissible negative intercept is
transcendental. This is the affine identity for `shiftedConstant`, combined
with independence of the first positive-intercept block and `1`. -/
theorem shiftedConstant_transcendental_of_fixedSlope
    (published : FixedSlopeAlgebraicIndependenceInput)
    (a r : ℕ) (ha : 1 ≤ a) (hr₂ : 2 ≤ r) (hr : r ≤ a) :
    Transcendental ℚ (shiftedConstant a r) := by
  have hblock := fixedSlopeBlock_linearIndependent published a 1 ha (le_rfl)
  let previous : Fin (a + 1) := ⟨r - 2, by omega⟩
  let next : Fin (a + 1) := ⟨r - 1, by omega⟩
  have hne : previous ≠ next := by
    intro h
    have := congrArg Fin.val h
    simp [previous, next] at this
    omega
  let c₀ : RealAlgebraic := (1 / (r.factorial : ℚ))
  let c : Fin (a + 1) → RealAlgebraic := fun i ↦
    if i = next then (a + 1 - r : ℚ) / (a + 1 : ℚ)
    else if i = previous then 1 / (a + 1 : ℚ)
    else 0
  have hc : ∃ i, c i ≠ 0 := by
    refine ⟨previous, ?_⟩
    simp only [c, if_neg hne, if_pos]
    apply div_ne_zero
    · exact one_ne_zero
    · exact (map_ne_zero (algebraMap ℚ RealAlgebraic)).mpr (by positivity)
  have hsum :
      ∑ i, c i • fixedSlopeBlock a 1 i =
        c next • fixedSlopeBlock a 1 next +
          c previous • fixedSlopeBlock a 1 previous := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ previous)]
    congr 1
    apply Finset.sum_eq_single next
    · intro i hi hine
      have hiprev : i ≠ previous := (Finset.mem_erase.mp hi).1
      simp [c, hine, hiprev]
    · intro hnot
      exact (hnot (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)).elim
  apply affineCombination_transcendental hblock (shiftedConstant a r) c₀ c hc
  rw [hsum, shiftedConstant_affine a r ha (by omega)]
  have hr₁ : 1 + (r - 1) = r := by omega
  have hr₂ : 1 + (r - 2) = r - 1 := by omega
  simp [c₀, c, hne, fixedSlopeBlock, previous, next,
    IntermediateField.smul_def, smul_eq_mul, hr₁, hr₂]
  ring

/-- **Conditional affine theorem.** The manuscript's fixed-slope
algebraic-independence input implies transcendence for every positive
integer-valued affine function: `a ≥ 1` and `b ≥ 1 - a`. All reindexing,
recurrence propagation, and negative-intercept deductions are checked in Lean. -/
theorem integer_constant_transcendental_of_fixedSlope
    (published : FixedSlopeAlgebraicIndependenceInput)
    (a : ℕ) (b : ℤ) (ha : 1 ≤ a) (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    Transcendental ℚ (integerConstant a b) := by
  by_cases hb₀ : 0 ≤ b
  · rw [integerConstant_eq_constant_of_nonneg a b hb₀]
    exact nonnegative_constant_transcendental_of_fixedSlope published a b.toNat ha
  · have hbneg : b < 0 := lt_of_not_ge hb₀
    rw [integerConstant_eq_shifted a b hb]
    have hbase : 0 ≤ ((a + 1 : ℕ) : ℤ) + b := by
      push_cast
      omega
    have hr_cast : ((shiftedIntercept a b : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) + b :=
      Int.toNat_of_nonneg hbase
    have ha₂ : 2 ≤ a := by omega
    have hr₂ : 2 ≤ shiftedIntercept a b := by omega
    have hr : shiftedIntercept a b ≤ a := by omega
    exact shiftedConstant_transcendental_of_fixedSlope published a
      (shiftedIntercept a b) (by omega) hr₂ hr

/-- The rational linear span of `1` and the fixed-slope transcendence basis. -/
noncomputable def fixedSlopeAffineSpan (a : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.insert 1 (Set.range (fixedSlopeBasis a)))

private theorem rational_mem_fixedSlopeAffineSpan (a : ℕ) (q : ℚ) :
    (q : ℝ) ∈ fixedSlopeAffineSpan a := by
  have hone : (1 : ℝ) ∈ fixedSlopeAffineSpan a :=
    Submodule.subset_span (Set.mem_insert 1 (Set.range (fixedSlopeBasis a)))
  simpa using (fixedSlopeAffineSpan a).smul_mem q hone

/-- Every nonnegative-intercept value belongs to the rational affine span of
the fixed-slope basis. This packages the boundary and beyond-strip recurrences
as a single induction theorem. -/
theorem constant_mem_fixedSlopeAffineSpan (a b : ℕ) (ha : 1 ≤ a) :
    constant a b ∈ fixedSlopeAffineSpan a := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      by_cases hlt : b < a
      · let i : Fin (a + 1) := ⟨b, by omega⟩
        have hi : fixedSlopeBasis a i ∈ fixedSlopeAffineSpan a :=
          Submodule.subset_span
            (Set.mem_insert_of_mem (1 : ℝ) (Set.mem_range_self i))
        simpa [i, fixedSlopeBasis, hlt] using hi
      · by_cases heq : b = a
        · subst b
          rw [constant_boundary_eq a ha]
          have hzero : constant a 0 ∈ fixedSlopeAffineSpan a := ih 0 (by omega)
          have hrat₀ :=
            rational_mem_fixedSlopeAffineSpan a (1 / (a.factorial : ℚ))
          have hrat : (1 / (a.factorial : ℝ)) ∈ fixedSlopeAffineSpan a := by
            convert hrat₀ using 1; norm_num
          have hmul := (fixedSlopeAffineSpan a).smul_mem (a + 1 : ℚ) hzero
          convert Submodule.sub_mem (fixedSlopeAffineSpan a) hmul hrat using 1;
            simp [Rat.smul_def]
        · by_cases hnext : b = a + 1
          · subst b
            have hi : fixedSlopeBasis a (Fin.last a) ∈ fixedSlopeAffineSpan a :=
              Submodule.subset_span
                (Set.mem_insert_of_mem (1 : ℝ) (Set.mem_range_self (Fin.last a)))
            simpa [fixedSlopeBasis_last] using hi
          · have hbeyond : a + 1 < b := by omega
            have hprev : constant a (b - 1) ∈ fixedSlopeAffineSpan a :=
              ih (b - 1) (by omega)
            have hlow : constant a (b - a - 1) ∈ fixedSlopeAffineSpan a :=
              ih (b - a - 1) (by omega)
            have hrat₀ := rational_mem_fixedSlopeAffineSpan a
              ((a + 1 : ℚ) / (b.factorial : ℚ))
            have hrat : ((a + 1 : ℝ) / (b.factorial : ℝ)) ∈
              fixedSlopeAffineSpan a := by
              convert hrat₀ using 1; norm_num
            have hmul := (fixedSlopeAffineSpan a).smul_mem (a + 1 : ℚ) hlow
            have hinside :
                constant a (b - 1) - (a + 1 : ℚ) • constant a (b - a - 1) +
                    (a + 1 : ℝ) / (b.factorial : ℝ) ∈ fixedSlopeAffineSpan a :=
              Submodule.add_mem (fixedSlopeAffineSpan a)
                (Submodule.sub_mem (fixedSlopeAffineSpan a) hprev hmul) hrat
            have hscaled := (fixedSlopeAffineSpan a).smul_mem
              (1 / (b - a - 1 : ℚ)) hinside
            rw [constant_beyond_recurrence a b ha hbeyond]
            convert hscaled using 1; simp [Rat.smul_def]
            field_simp

/-- Every admissible integer-intercept value lies in the same rational affine
span. Together with the basis independence, this is the formal fixed-slope
structure asserted in the manuscript. -/
theorem integerConstant_mem_fixedSlopeAffineSpan
    (a : ℕ) (b : ℤ) (ha : 1 ≤ a) (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    integerConstant a b ∈ fixedSlopeAffineSpan a := by
  by_cases hb₀ : 0 ≤ b
  · rw [integerConstant_eq_constant_of_nonneg a b hb₀]
    exact constant_mem_fixedSlopeAffineSpan a b.toNat ha
  · have hbneg : b < 0 := lt_of_not_ge hb₀
    rw [integerConstant_eq_shifted a b hb]
    have hbase : 0 ≤ ((a + 1 : ℕ) : ℤ) + b := by
      push_cast
      omega
    have hr_cast : ((shiftedIntercept a b : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) + b :=
      Int.toNat_of_nonneg hbase
    let r := shiftedIntercept a b
    have hr₁ : 1 ≤ r := by omega
    have hra : r ≤ a := by omega
    rw [shiftedConstant_affine a r ha hr₁]
    have hrat₀ := rational_mem_fixedSlopeAffineSpan a (1 / (r.factorial : ℚ))
    have hrat : (1 / (r.factorial : ℝ)) ∈ fixedSlopeAffineSpan a := by
      convert hrat₀ using 1; norm_num
    have hrmem : constant a r ∈ fixedSlopeAffineSpan a :=
      constant_mem_fixedSlopeAffineSpan a r ha
    have hprevmem : constant a (r - 1) ∈ fixedSlopeAffineSpan a :=
      constant_mem_fixedSlopeAffineSpan a (r - 1) ha
    have h₁ := (fixedSlopeAffineSpan a).smul_mem
      (((a + 1 - r : ℕ) : ℚ) / (a + 1 : ℚ)) hrmem
    have h₂ := (fixedSlopeAffineSpan a).smul_mem
      (1 / (a + 1 : ℚ)) hprevmem
    have hsub : ((a + 1 - r : ℕ) : ℝ) = (a + 1 : ℝ) - r := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    convert Submodule.add_mem (fixedSlopeAffineSpan a)
      (Submodule.add_mem (fixedSlopeAffineSpan a) hrat h₁) h₂ using 1;
        norm_num [Rat.smul_def, hsub]

/-- The fixed-slope basis is algebraically independent over `ℚ`, conditional on
the explicit analytic input. -/
theorem fixedSlopeBasis_algebraicIndependent
    (published : FixedSlopeAlgebraicIndependenceInput) (a : ℕ) (ha : 1 ≤ a) :
    AlgebraicIndependent ℚ (fixedSlopeBasis a) :=
  published.independent a ha

/-- Algebraic independence persists after extending the coefficient field from
`ℚ` to the subfield of real numbers algebraic over `ℚ`. This is the real-valued
form of independence over `Q̄` used by the manuscript. -/
theorem fixedSlopeBasis_algebraicIndependent_realAlgebraic
    (published : FixedSlopeAlgebraicIndependenceInput) (a : ℕ) (ha : 1 ≤ a) :
    AlgebraicIndependent RealAlgebraic (fixedSlopeBasis a) :=
  (published.independent a ha).algebraicClosure

/-- Every member of the fixed-slope basis is transcendental. -/
theorem fixedSlopeBasis_transcendental
    (published : FixedSlopeAlgebraicIndependenceInput) (a : ℕ) (ha : 1 ≤ a)
    (i : Fin (a + 1)) :
    Transcendental ℚ (fixedSlopeBasis a i) :=
  (published.independent a ha).transcendental i

/-- Evaluation identifies the polynomial algebra on `a + 1` variables with the
algebra generated by the fixed-slope basis. This packages the statement that the
basis has no polynomial relations. -/
noncomputable def fixedSlopePolynomialEquiv
    (published : FixedSlopeAlgebraicIndependenceInput) (a : ℕ) (ha : 1 ≤ a) :
    MvPolynomial (Fin (a + 1)) ℚ ≃ₐ[ℚ]
      Algebra.adjoin ℚ (Set.range (fixedSlopeBasis a)) :=
  (published.independent a ha).aevalEquiv

private theorem fixedSlopeAffineSpan_le_adjoin (a : ℕ) :
    fixedSlopeAffineSpan a ≤
      (Algebra.adjoin ℚ (Set.range (fixedSlopeBasis a))).toSubmodule := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with (rfl | ⟨i, rfl⟩)
  · exact (Algebra.adjoin ℚ (Set.range (fixedSlopeBasis a))).one_mem
  · exact Algebra.subset_adjoin (Set.mem_range_self i)

/-- The algebra generated by all nonnegative-intercept values is exactly the
algebra generated by the `a + 1` fixed-slope basis values. -/
theorem fixedSlopeConstants_adjoin_eq
    (a : ℕ) (ha : 1 ≤ a) :
    Algebra.adjoin ℚ (Set.range (constant a)) =
      Algebra.adjoin ℚ (Set.range (fixedSlopeBasis a)) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨b, rfl⟩
    exact fixedSlopeAffineSpan_le_adjoin a
      (constant_mem_fixedSlopeAffineSpan a b ha)
  · apply Algebra.adjoin_le
    rintro x ⟨i, rfl⟩
    by_cases hi : i.1 < a
    · rw [fixedSlopeBasis_of_lt a i hi]
      exact Algebra.subset_adjoin (Set.mem_range_self i.1)
    · have hilast : i.1 = a := by omega
      rw [fixedSlopeBasis, if_neg hi]
      exact Algebra.subset_adjoin (Set.mem_range_self (a + 1))

/-- The algebra generated by the fixed-slope family has transcendence degree
exactly `a + 1`. This is the formal version of the manuscript's maximality
statement for each fixed slope. -/
theorem fixedSlopeConstants_trdeg
    (published : FixedSlopeAlgebraicIndependenceInput)
    (a : ℕ) (ha : 1 ≤ a) :
    Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range (constant a))) = (a + 1 : Cardinal) := by
  rw [fixedSlopeConstants_adjoin_eq a ha]
  rw [← (fixedSlopePolynomialEquiv published a ha).trdeg_eq]
  rw [MvPolynomial.trdeg_of_isDomain]
  simp

end FactorialRatio
