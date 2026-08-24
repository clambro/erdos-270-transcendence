# Lean formalization

**[Read the full paper (PDF)](../Algebraic_Independence_in_the_Affine_Case_of_Erdos_Problem_270.pdf)**

**[Return to the project overview](../README.md)**

This is the Lean 4 formalization accompanying *Algebraic Independence in the Affine Case of Erdős Problem 270*. The elementary irrationality theorem is fully formalized. For the transcendence and algebraic-independence results, Lean verifies the algebraic deductions from explicitly stated inputs, while the E-function and differential-equation results remain external.

## Verification summary

| Result | Lean status | External inputs |
| --- | --- | --- |
| Irrationality of $C_{a,b}$ for $a\geq1$ and $0\leq b\leq a$ | Fully verified | None |
| Transcendence of $C_{1,0}$ by the Gaussian argument | Conditional deduction verified | Gaussian identity; Siegel–Shidlovsky value independence |
| Algebraic independence of $C_{a,0},\ldots,C_{a,a-1},C_{a,a+1}$ | Conditional deduction verified | Salikhov and Viskina–Salikhov algebraic independence; logarithmic boundary obstruction; trace descent; Beukers's theorem |
| Transcendence of every $C_{a,b}$ with $a\geq1$ and $b\geq1-a$ | Conditional deduction verified | The fixed-slope algebraic-independence input above |
| Rational affine-span structure and fixed-slope transcendence degree $a+1$ | Conditional deduction verified | The fixed-slope algebraic-independence input above |

## Irrationality theorem

The main unconditional result is [`constant_irrational`](FactorialRatio/ElementaryIrrationality.lean):

```lean
theorem constant_irrational (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ a) :
    Irrational (constant a b)
```

Here `constant a b` denotes

$$
C_{a,b}=\sum_{n=1}^{\infty}\frac{n!}{((a+1)n+b)!}.
$$

Lean proves convergence, the divisibility chain for the reciprocal denominators, integrality of the scaled partial sums, positivity of the tail, an explicit bound forcing the scaled tail to zero, and the contradiction with rationality. Convergence is also proved for every $a\geq1$ and $b\geq0$; only the divisibility proof requires $b\leq a$.

## Coefficient and value identities

The following parts of the later argument are verified without additional mathematical assumptions:

- the reindexing

  $$
  C_{1,0}=\frac12\sum_{n=0}^{\infty}\frac{n!}{(2n+1)!};
  $$

- the normalization $F_{a,b}(1)=1+b!C_{a,b}$ and convergence of the normalized and Euler-derivative series;
- the reduction of every integer intercept $b\geq1-a$ to a nonnegative-intercept or shifted series;
- the coefficientwise and special-value contiguous identity relating $F_{a,b-1}$, $F_{a,b}$, and $\theta F_{a,b}$;
- the boundary identity (16), the recurrence (17) for larger nonnegative intercepts, and the affine negative-intercept identity (18).

These calculations appear in [`ValueIdentities.lean`](FactorialRatio/ValueIdentities.lean) and [`CoefficientIdentities.lean`](FactorialRatio/CoefficientIdentities.lean). The analytic differential modules are not constructed in Lean.

## Base-case transcendence

[`BaseCaseTranscendence.lean`](FactorialRatio/BaseCaseTranscendence.lean) contains the theorem

```lean
theorem constant_one_zero_transcendental_of_gaussian
    (gaussian : BaseCaseGaussianIdentity)
    (siegelShidlovsky : BaseCaseSiegelShidlovskyInput) :
    Transcendental ℚ (constant 1 0)
```

The two hypotheses are defined in [`ExternalTheorems.lean`](FactorialRatio/ExternalTheorems.lean). They state the Gaussian representation of $C_{1,0}$ recorded by Crmarić and Kovač and the special-value linear independence supplied by the Siegel–Shidlovsky theorem.

From these hypotheses, Lean derives

$$
y(1/4)=2C_{1,0}e^{-1/4}
$$

and proves that algebraicity of $C_{1,0}$ would contradict the stated independence. The Gaussian representation and the Siegel–Shidlovsky theorem have not been formalized.

## Fixed-slope algebraic independence

The proposed basis at slope $a$ is represented by [`fixedSlopeBasis`](FactorialRatio/ValueIdentities.lean):

```lean
noncomputable def fixedSlopeBasis (a : ℕ) (i : Fin (a + 1)) : ℝ :=
  if i.1 < a then constant a i.1 else constant a (a + 1)
```

[`FixedSlopeAlgebraicIndependence.lean`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean) proves, conditional on `FixedSlopeAlgebraicIndependenceInput`, that this family is algebraically independent over $\mathbb Q$, remains independent after extending coefficients to the real algebraic numbers, and generates a polynomial algebra on $a+1$ variables.

The file now carries the manuscript's remaining algebraic argument through to its endpoint. Lean verifies that the boundary identity gives an independent block $C_{a,1},\ldots,C_{a,a+1}$ and that each recurrence replaces one member of an independent block with the next value by an invertible affine transformation. It then proves:

- [`fixedSlopeBlock_linearIndependent`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean): every consecutive block of $a+1$ positive-intercept values, together with $1$, is linearly independent over the real algebraic numbers;
- [`integer_constant_transcendental_of_fixedSlope`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean): every integer-intercept value with $b\geq1-a$ is transcendental;
- [`integerConstant_mem_fixedSlopeAffineSpan`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean): every such value lies in the rational affine span of the basis;
- [`fixedSlopeConstants_adjoin_eq`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean): all nonnegative-intercept values generate the same $\mathbb Q$-algebra as the basis;
- [`fixedSlopeConstants_trdeg`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean): that algebra has transcendence degree exactly $a+1$.

The external input packages the analytic part of the manuscript: the Salikhov and Viskina–Salikhov results, the log-free formal field at infinity, the trace-descent argument for the additional function, and Beukers's specialization theorem. These ingredients have not been reconstructed in Lean.

## Source guide

- [`FactorialRatio.lean`](FactorialRatio.lean) — library entry point.
- [`Definitions.lean`](FactorialRatio/Definitions.lean) — series, constants, reciprocal denominators, and integer-intercept definitions.
- [`ElementaryIrrationality.lean`](FactorialRatio/ElementaryIrrationality.lean) — convergence, denominator divisibility, tail estimates, and irrationality.
- [`CoefficientIdentities.lean`](FactorialRatio/CoefficientIdentities.lean) — coefficientwise contiguous and negative-intercept identities.
- [`ValueIdentities.lean`](FactorialRatio/ValueIdentities.lean) — special-value identities, reindexing, and negative-intercept reductions.
- [`ExternalTheorems.lean`](FactorialRatio/ExternalTheorems.lean) — interfaces for the unformalized transcendence inputs.
- [`BaseCaseTranscendence.lean`](FactorialRatio/BaseCaseTranscendence.lean) — base-case transcendence from the two stated inputs.
- [`FixedSlopeAlgebraicIndependence.lean`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean) — conditional fixed-slope algebraic independence, recurrence propagation, affine-span structure, all-intercept transcendence, and exact transcendence degree.
- [`AxiomAudit.lean`](FactorialRatio/AxiomAudit.lean) — axiom checks for the principal results.

## Build and axiom audit

The project pins Lean and mathlib to version 4.33.1. With Lean installed through `elan`, run these commands from the `formalization` directory:

```bash
lake build
lake env lean FactorialRatio/AxiomAudit.lean
```

The audit reports only Lean's standard foundational axioms:

```text
[propext, Classical.choice, Quot.sound]
```

There are no `sorry`, `admit`, or global `axiom` declarations. The conditional transcendence theorems still require the structures listed above as hypotheses; the audit confirms that none has been added to Lean's global environment.
