# Lean formalization

**[Read the full paper (PDF)](../Algebraic_Independence_in_the_Affine_Case_of_Erdos_Problem_270.pdf)**

**[Return to the project overview](../README.md)**

This directory contains the Lean 4 formalization accompanying *Algebraic Independence in the Affine Case of Erdős Problem 270*. The elementary irrationality theorem is fully formalized. For the transcendence and algebraic-independence results, Lean verifies the algebraic deductions from explicitly stated inputs, while the E-function and differential-equation results themselves remain external.

## Verification summary

| Result | Lean status | External inputs |
| --- | --- | --- |
| Irrationality of $C_{a,b}$ for $a\geq1$ and $0\leq b\leq a$ | Fully verified | None |
| Transcendence of $C_{1,0}$ by the Gaussian argument | Conditional deduction verified | Gaussian identity; Siegel–Shidlovsky value independence |
| Transcendence of $C_{a,b}$ for $a\geq1$ and $b\geq1-a$ | Conditional deduction verified | Salikhov and Salikhov–Viskina value independence; formal minimality at infinity; Beukers's lifting theorem |
| Algebraic independence of $C_{a,0},\ldots,C_{a,a-1},C_{a,a+1}$ | Conditional algebraic consequences verified | Salikhov and Salikhov–Viskina algebraic independence; logarithmic boundary obstruction; trace descent; Beukers's theorem |

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

## Identities used in the transcendence proof

The following parts of the later argument are verified without additional mathematical assumptions:

- the reindexing

  $$
  C_{1,0}=\frac12\sum_{n=0}^{\infty}\frac{n!}{(2n+1)!};
  $$

- the normalization $F_{a,b}(1)=1+b!C_{a,b}$ and convergence of the normalized and Euler-derivative series;
- the reduction of every integer intercept $b\geq1-a$ to a nonnegative-intercept or shifted series;
- the decomposition $b=q(a+1)+r$ and the coefficientwise Euler-operator identity for $b>a$;
- the recurrence associated with the inhomogeneous differential equation;
- the resonant vanishing, the nonzero forcing term, and the forced coefficient of $z^{-a}\log z$.
- the coefficientwise and special-value contiguous identity relating $F_{a,b-1}$, $F_{a,b}$, and $\theta F_{a,b}$.
- the boundary identity (31), the recurrence (32) for larger nonnegative intercepts, and the affine negative-intercept identity (33).

These calculations appear in [`ValueIdentities.lean`](FactorialRatio/ValueIdentities.lean) and [`CoefficientIdentities.lean`](FactorialRatio/CoefficientIdentities.lean). They establish the algebraic and coefficient-level identities used in the manuscript. The analytic differential modules needed for the general transcendence theorem are not constructed in Lean.

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

## Full affine family

The manuscript's main theorem covers every positive integer-valued affine function, corresponding to $a\geq1$ and $b\geq1-a$. Its Lean statement is [`integer_constant_transcendental`](FactorialRatio/Main.lean):

```lean
theorem integer_constant_transcendental
    (fundamental : FundamentalStripInput)
    (beyond : BeyondStripInput)
    (a : ℕ) (b : ℤ) (ha : 1 ≤ a) (hb : (1 : ℤ) - (a : ℤ) ≤ b) :
    Transcendental ℚ (integerConstant a b)
```

`FundamentalStripInput` records the value-independence statements used for $0\leq b\leq a$ and the shifted negative-intercept cases. `BeyondStripInput` records the value-independence statement used for $b>a$. Given these hypotheses, Lean checks the normalization, all parameter-range reductions, and the final transcendence deductions.

The following parts of the paper remain outside the formalization:

- the Salikhov and Salikhov–Viskina theorems and their application to the relevant hypergeometric $E$-functions;
- the analytic hypergeometric differential systems;
- descent of functional relations from $\mathbb C(z)$ to $\overline{\mathbb Q}(z)$;
- the formal differential module at infinity, its Levelt–Turrittin decomposition, and the zero-exponential projection;
- the deduction of functional minimality from the logarithmic resonance;
- Beukers's lifting theorem.

The input structures are theorem hypotheses, not global Lean axioms. [`ExternalTheorems.lean`](FactorialRatio/ExternalTheorems.lean) gives their exact statements.

## Fixed-slope algebraic independence

The proposed basis at slope $a$ is represented by [`fixedSlopeBasis`](FactorialRatio/ValueIdentities.lean):

```lean
noncomputable def fixedSlopeBasis (a : ℕ) (i : Fin (a + 1)) : ℝ :=
  if i.1 < a then constant a i.1 else constant a (a + 1)
```

[`FixedSlopeAlgebraicIndependence.lean`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean) proves, conditional on the explicit `FixedSlopeAlgebraicIndependenceInput`, that this family is algebraically independent over $\mathbb Q$, remains independent after extending coefficients to the real algebraic numbers, and generates a polynomial algebra on $a+1$ variables. It also derives the transcendence of every basis coordinate. [`ValueIdentities.lean`](FactorialRatio/ValueIdentities.lean) independently verifies the exact recurrences that place all remaining admissible intercepts in the rational affine span of this basis; the induction over arbitrary intercepts and the resulting transcendence-degree statement have not yet been packaged as a single Lean theorem.

The external input packages the analytic part of the manuscript: the Salikhov and Salikhov–Viskina results, the log-free formal field at infinity, the trace-descent argument for the boundary function, and Beukers's specialization theorem. These ingredients have not been reconstructed in Lean.

## Source guide

- [`FactorialRatio.lean`](FactorialRatio.lean) — library entry point.
- [`Definitions.lean`](FactorialRatio/Definitions.lean) — series, constants, reciprocal denominators, and integer-intercept definitions.
- [`ElementaryIrrationality.lean`](FactorialRatio/ElementaryIrrationality.lean) — convergence, denominator divisibility, tail estimates, and irrationality.
- [`CoefficientIdentities.lean`](FactorialRatio/CoefficientIdentities.lean) — Euler reduction, differential-equation coefficients, and resonance calculations.
- [`ValueIdentities.lean`](FactorialRatio/ValueIdentities.lean) — special-value identities, reindexing, and negative-intercept reductions.
- [`ExternalTheorems.lean`](FactorialRatio/ExternalTheorems.lean) — interfaces for the unformalized transcendence inputs.
- [`BaseCaseTranscendence.lean`](FactorialRatio/BaseCaseTranscendence.lean) — base-case transcendence from the two stated inputs.
- [`Main.lean`](FactorialRatio/Main.lean) — main theorem statements and final deductions.
- [`FixedSlopeAlgebraicIndependence.lean`](FactorialRatio/FixedSlopeAlgebraicIndependence.lean) — conditional fixed-slope algebraic independence and its algebraic consequences.
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
