# Algebraic Independence in the Affine Case of Erdős Problem 270

**[Read the full paper (PDF)](Algebraic_Independence_in_the_Affine_Case_of_Erdos_Problem_270.pdf)**

**[Browse the Lean proofs and verification notes](formalization/README.md)**

## Contents

- [Introduction](#introduction)
- [Proof outline](#proof-outline)
  - [1. Irrationality of the base case](#1-irrationality-of-the-base-case)
  - [2. Irrationality for $0\leq b\leq a$](#irrationality-range)
  - [3. Transcendence of the base case](#3-transcendence-of-the-base-case)
  - [4. Hypergeometric transcendence for the affine family](#4-hypergeometric-transcendence-for-the-affine-family)
  - [5. Algebraic independence at fixed slope](#5-algebraic-independence-at-fixed-slope)
- [Lean verification](#lean-verification)
  - [Fully verified](#fully-verified)
  - [Not yet verified in Lean](#not-yet-verified-in-lean)
  - [Reproducing the Lean build](#reproducing-the-lean-build)

## Introduction

Erdős Problem 270 concerns the series

$$
S(f)=\sum_{n=1}^{\infty}\frac{1}{(n+1)(n+2)\cdots(n+f(n))}.
$$

For the affine choice $f(n)=an+b$, this becomes

$$
C_{a,b}=\sum_{n=1}^{\infty}\frac{n!}{((a+1)n+b)!}.
$$

The main result determines the algebraic structure of the family at each fixed slope. For every $a\geq1$, the $a+1$ constants

$$
C_{a,0},C_{a,1},\ldots,C_{a,a-1},C_{a,a+1}
$$

are algebraically independent, and every other admissible intercept is a rational affine combination of them. Consequently the fixed-slope family has transcendence degree $a+1$, and every $C_{a,b}$ with $b\geq1-a$ is transcendental. The argument develops from elementary irrationality proofs through the hypergeometric $E$-function machinery needed for the algebraic-independence theorem.

## Proof outline

The complete arguments and references are in the [full paper](Algebraic_Independence_in_the_Affine_Case_of_Erdos_Problem_270.pdf).

### 1. Irrationality of the base case

Note: Crmarić and Kovač had already noticed this same argument for the base case after their paper appeared, and Kovač posted it on the [Erdős Problems forum](https://www.erdosproblems.com/forum/thread/270#post-7469) in July 2026. We became aware of the post after independently discovering the argument.

For

$$
C_{1,0}=\sum_{n=1}^{\infty}\frac{n!}{(2n)!}=\sum_{n=1}^{\infty}\frac1{D_n},
\qquad D_n=\frac{(2n)!}{n!},
$$

the denominators form a divisibility chain because

$$
\frac{D_{n+1}}{D_n}=4n+2.
$$

If $P_N$ is the $N^\mathrm{th}$ partial sum and $R_N=C_{1,0}-P_N$, then $D_NP_N$ is an integer, while a geometric estimate gives

$$
0 < D_N R_N \leq \frac{1}{4N+1} \to 0.
$$

If $C_{1,0}=p/q$ were rational, then $D_NR_N=pD_N/q-D_NP_N$ would be a positive element of $q^{-1}\mathbb Z$. It would therefore be at least $1/q$, contradicting the limit above. Hence $C_{1,0}$ is irrational.

<a id="irrationality-range"></a>

### 2. Irrationality for $0\leq b\leq a$

The same argument works for $a\geq1$ and $0\leq b\leq a$. Set

$$
D_n=\frac{((a+1)n+b)!}{n!}.
$$

In the quotient $D_{n+1}/D_n$, one of the $a+1$ consecutive numerator factors is $(a+1)(n+1)$, so the factor $n+1$ in the denominator cancels. Thus

$$
r_n:=\frac{D_{n+1}}{D_n}
$$

is a positive integer. Moreover, $r_n\to\infty$. The same partial-sum argument now gives

$$
0 < D_N R_N
= \sum_{k\geq1}\frac{1}{r_N r_{N+1}\cdots r_{N+k-1}}
\leq \frac{1}{r_N-1}
\to 0.
$$

Rationality would again force $D_NR_N$ to remain at least $1/q$. Therefore $C_{a,b}$ is irrational throughout this range.

### 3. Transcendence of the base case

Crmarić and Kovač record the Gaussian representation

$$
C_{1,0}=e^{1/4}\int_0^{1/2}e^{-t^2}\,dt.
$$

Define

$$
y(x)=\frac1{\sqrt{x}}\int_0^{\sqrt{x}}e^{-t^2}\,dt.
$$

A 2023 MathOverflow argument applies the Siegel–Shidlovsky theorem to this $E$-function and $e^{-x}$. The same argument at $x=1/4$ gives the algebraic independence of $y(1/4)$ and $e^{-1/4}$. Since

$$
y(1/4)=2\int_0^{1/2}e^{-t^2}\,dt
=2C_{1,0}e^{-1/4},
$$

an algebraic value of $C_{1,0}$ would produce a nontrivial algebraic relation between those two values. Hence $C_{1,0}$ is transcendental.

### 4. Hypergeometric transcendence for the affine family

For $b\geq0$, introduce the normalized hypergeometric $E$-function

$$
F_{a,b}(z)=b!\sum_{n=0}^{\infty}\frac{n!}{((a+1)n+b)!}z^{an},
\qquad F_{a,b}(1)=1+b!C_{a,b}.
$$

When $0\leq b\leq a$, the multiplication formula expresses $F_{a,b}$ as a ${}_1F_a$ function. The value-independence theorems of Salikhov for odd $a$ and Salikhov–Viskina for even $a$ then give the transcendence of $F_{a,b}(1)$. The cases $1-a\leq b<0$ reduce to this range by shifting the summation index; the shifted value is an explicit algebraic linear combination of $F_{a,r}(1)$ and its Euler derivative.

For $b>a$, write

$$
b=q(a+1)+r,
\qquad q\geq1,
\qquad 0\leq r\leq a.
$$

Coefficient comparison gives an Euler-operator reduction from $F_{a,b}$ to $F_{a,r}$. At infinity, the differential module associated with $F_{a,r}$ has a rank-one zero-exponential component whose Laurent series contains no logarithms. Projecting the Euler reduction onto this component creates a resonance: the Euler operator kills the relevant log-free $z^{-a}$ coefficient, while the right side has a nonzero $z^{-a}$ term. The missing term can only be supplied by $z^{-a}\log z$. This proves that $F_{a,b}$ lies outside the differential space generated by $F_{a,r}$ and establishes the functional independence required in the final step.

Beukers's refinement of the Siegel–Shidlovsky theorem lifts that functional independence to linear independence of the values at the ordinary point $z=1$. Consequently $F_{a,b}(1)$, and therefore $C_{a,b}$, is transcendental. Combining the three parameter ranges gives the theorem

$$
\boxed{C_{a,b}\text{ is transcendental for every }a\geq1,\ b\geq1-a.}
$$

### 5. Algebraic independence at fixed slope

[Christopher D. Long suggested](https://x.com/octonion/status/2091555025197662264) that the transcendence argument might extend to algebraic independence. For each fixed $a$, the resulting independent family is

$$
C_{a,0},C_{a,1},\ldots,C_{a,a-1},C_{a,a+1}.
$$

The contiguous relation

$$
F_{a,b-1}=F_{a,b}+\frac{a+1}{ab}\theta F_{a,b}
$$

identifies the first $a$ functions with an invertible triangular transformation of one fundamental-strip function and its first $a-1$ Euler derivatives. The algebraic-independence criteria of Salikhov and Salikhov–Viskina therefore give the independence of these first $a$ functions.

The remaining boundary function $G=F_{a,a+1}$ satisfies

$$
\left(\frac\theta a+1\right)G=(a+1)!z^{-a}(F_{a,0}-1).
$$

The field generated by the first $a$ functions has log-free formal expansions at infinity, while this equation forces the zero-exponential component of $G$ to contain $-a(a+1)!z^{-a}\log z$. A field-trace argument then shows that $G$ is transcendental over the preceding differential field. Beukers's theorem transfers the resulting functional algebraic independence to the values at $z=1$.

Exact recurrences express every other $C_{a,b}$ as a rational affine combination of this basis. Consequently

$$
\boxed{
\operatorname{trdeg}_{\overline{\mathbb Q}}
\overline{\mathbb Q}(C_{a,b}:b\geq1-a)=a+1.
}
$$

## Lean verification

The detailed verification report is in the [formalization README](formalization/README.md). The project uses Lean 4.33.1 and mathlib 4.33.1.

### Fully verified

The elementary irrationality theorem for $a\geq1$ and $0\leq b\leq a$ is proved without additional mathematical assumptions in [`ElementaryIrrationality.lean`](formalization/FactorialRatio/ElementaryIrrationality.lean). Lean checks convergence, the denominator divisibility chain, integrality of the scaled partial sums, positivity of the tail, its decay to zero, and the final rationality contradiction.

Lean also verifies many of the algebraic reductions used later:

- the base-case reindexing $C_{1,0}=\frac12\sum_{n\geq0}n!/(2n+1)!$, convergence of that series, the normalization $F_{a,b}(1)=1+b!C_{a,b}$, and the negative-intercept identities in [`ValueIdentities.lean`](formalization/FactorialRatio/ValueIdentities.lean);
- the Euclidean decomposition of $b$, the coefficientwise Euler reduction, the differential-equation recurrence, the resonant vanishing, the nonzero forcing coefficient, and the forced logarithmic coefficient in [`CoefficientIdentities.lean`](formalization/FactorialRatio/CoefficientIdentities.lean);
- the deduction of the base-case transcendence statement from the Gaussian identity and the required Siegel–Shidlovsky value independence in [`BaseCaseTranscendence.lean`](formalization/FactorialRatio/BaseCaseTranscendence.lean);
- the normalization, parameter-range case split, and negative-intercept reduction in the conditional main theorem in [`Main.lean`](formalization/FactorialRatio/Main.lean).
- the construction of the $a+1$-element fixed-slope basis, extension of algebraic independence from rational to real algebraic coefficients, transcendence of each basis coordinate, and the resulting polynomial-algebra equivalence in [`FixedSlopeAlgebraicIndependence.lean`](formalization/FactorialRatio/FixedSlopeAlgebraicIndependence.lean), conditional on the explicitly stated analytic independence input.
- the exact fixed-slope boundary, beyond-boundary, and negative-intercept affine recurrences in [`ValueIdentities.lean`](formalization/FactorialRatio/ValueIdentities.lean).

There are no `sorry`, `admit`, or global `axiom` declarations. The [axiom audit](formalization/FactorialRatio/AxiomAudit.lean) reports only Lean's standard foundational axioms.

### Not yet verified in Lean

The formalization does **not** currently prove the manuscript's transcendence and algebraic-independence results unconditionally. The missing inputs are stated explicitly in [`ExternalTheorems.lean`](formalization/FactorialRatio/ExternalTheorems.lean). They include:

- the Gaussian integral identity and the Siegel–Shidlovsky theorem used in the shorter base-case argument;
- the applications of the Salikhov and Salikhov–Viskina value-independence theorems;
- the analytic hypergeometric-function and differential-system setup;
- the Levelt–Turrittin decomposition and the zero-exponential projection at infinity;
- the passage from the verified resonance calculation to functional minimality;
- the application of Beukers's lifting theorem.
- the stronger log-free formal-field and trace-descent steps used to prove fixed-slope algebraic independence.

The general transcendence result in [`Main.lean`](formalization/FactorialRatio/Main.lean) is therefore conditional on the explicit literature-dependent interfaces in [`ExternalTheorems.lean`](formalization/FactorialRatio/ExternalTheorems.lean). Lean verifies the deduction from those interfaces, but not the interfaces themselves.

### Reproducing the Lean build

From the `formalization` directory, run:

```bash
lake build
lake env lean FactorialRatio/AxiomAudit.lean
```
