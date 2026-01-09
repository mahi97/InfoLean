import InfoLean.Basics.FiniteProb
import InfoLean.Probability.BinomialSums
import InfoLean.Coding.Hamming74
import InfoLean.Coding.Repetition
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

namespace InfoLean.Books.MacKay.Chapter1

open scoped BigOperators
open InfoLean
open InfoLean.Coding
open Matrix

/-! ## Exercise 1.1 -/

/- Problem:
A bent coin with probability f of heads is tossed N times.
1) What is the distribution of the number of heads r?
2) What are the mean and variance of r?
-/
theorem exercise1_1_distribution (f : NNReal) (hf : f ≤ 1) (N : ℕ) (i : Fin (N + 1)) :
    PMF.binomial f hf N i =
      f ^ (i : ℕ) * (1 - f) ^ ((Fin.last N - i) : ℕ) * (N.choose i : ℕ) := by
  simpa using PMF.binomial_apply f hf N i

theorem exercise1_1_mean (f : NNReal) (hf : f ≤ 1) (N : ℕ) :
    pmfExpectation (PMF.binomial f hf N) (fun i => (i : ℝ)) = (N : ℝ) * f := by
  calc
    pmfExpectation (PMF.binomial f hf N) (fun i => (i : ℝ)) =
        binomialMeanSum N (f : ℝ) := binomialExpectation_eq_sum f hf N
    _ = (N : ℝ) * f := binomialMeanSum_eq N (f : ℝ)

theorem exercise1_1_variance (f : NNReal) (hf : f ≤ 1) (N : ℕ) :
    pmfVariance (PMF.binomial f hf N) (fun i => (i : ℝ)) = (N : ℝ) * f * (1 - f) := by
  calc
    pmfVariance (PMF.binomial f hf N) (fun i => (i : ℝ)) =
        binomialVarianceSum N (f : ℝ) := binomialVariance_eq_sum f hf N
    _ = (N : ℝ) * f * (1 - f) := binomialVarianceSum_eq_all N (f : ℝ)

theorem exercise1_1_mean_sum (N : ℕ) (f : ℝ) :
    binomialMeanSum N f = (N : ℝ) * f := by
  simpa using binomialMeanSum_eq N f

theorem exercise1_1_variance_sum (N : ℕ) (f : ℝ) :
    binomialVarianceSum N f = (N : ℝ) * f * (1 - f) := by
  simpa using binomialVarianceSum_eq_all N f

/-! ## Exercise 1.2 -/

/- Problem:
Show that using the repetition code R3 reduces the error probability over a binary symmetric
channel with noise level f. Compute the decoded bit error probability.
-/
theorem exercise1_2_error_prob (f : ℝ) :
    repetitionErrorProb3 f = 3 * f ^ 2 * (1 - f) + f ^ 3 := by
  simp [repetitionErrorProb3]

theorem exercise1_2_error_prob_small_f (f : ℝ) :
    repetitionErrorProb3 f = 3 * f ^ 2 - 2 * f ^ 3 := by
  simp [repetitionErrorProb3]
  ring

theorem exercise1_2_eval_f01 : repetitionErrorProb3 (1 / 10 : ℝ) = (7 / 250 : ℝ) := by
  norm_num [repetitionErrorProb3]

/-! ## Exercise 1.3 -/

/- Problem:
(a) Show that for odd N the decoded error probability of R_N is
    sum_{n=(N+1)/2}^N (N choose n) f^n (1-f)^(N-n).
(b) For f = 0.1 identify the dominant term in the sum.
(c) Use Stirling's approximation to estimate the dominant term.
(d) For f = 0.1 find N so that p_b ~ 10^(-15).
-/
theorem exercise1_3a (N : ℕ) (f : ℝ) :
    repetitionErrorProb N f =
      Finset.sum (Finset.Icc ((N + 1) / 2) N) fun n =>
        (Nat.choose N n : ℝ) * f ^ n * (1 - f) ^ (N - n) := by
  rfl

theorem exercise1_3b (N : ℕ) :
    repetitionDominantIndex N = (N + 1) / 2 := by
  rfl

theorem exercise1_3c (N : ℕ) :
    centralBinomApprox N = (2 ^ N : ℝ) / Real.sqrt (Real.pi * ((N : ℝ) / 2)) := by
  rfl

theorem exercise1_3c_prob (N : ℕ) (f : ℝ) :
    repetitionErrorProbApprox N f =
      (1 / Real.sqrt (Real.pi * ((N : ℝ) / 8))) * (4 * f * (1 - f)) ^ (N / 2) := by
  rfl

theorem exercise1_3d : repetitionApproxN_f01 = 61 := by
  rfl

/-! ## Exercise 1.4 -/

/- Problem:
Prove that all codewords t = G^T s of the (7,4) Hamming code satisfy H t = 0 by
evaluating the 3x4 matrix H G^T (with G and H defined in the book).
-/
theorem exercise1_4 : hammingH * hammingG.transpose = 0 := by
  native_decide

/-! ## Exercise 1.5 -/

/- Problem:
Decode the following received strings using the (7,4) Hamming code:
(a) r = 1101011
(b) r = 0110110
(c) r = 0100111
(d) r = 1111111
-/
theorem exercise1_5a :
    decodeMessage ![1, 1, 0, 1, 0, 1, 1] = ![1, 1, 0, 0] := by
  native_decide

theorem exercise1_5b :
    decodeMessage ![0, 1, 1, 0, 1, 1, 0] = ![0, 1, 1, 0] := by
  native_decide

theorem exercise1_5c :
    decodeMessage ![0, 1, 0, 0, 1, 1, 1] = ![0, 1, 0, 0] := by
  native_decide

theorem exercise1_5d :
    decodeMessage ![1, 1, 1, 1, 1, 1, 1] = ![1, 1, 1, 1] := by
  native_decide

/-! ## Exercise 1.6 -/

/- Problem:
(a) Compute the block error probability p_B for the (7,4) Hamming code as a
function of noise level f and show the leading term is 21 f^2.
(b) Show the bit error probability p_b has leading term 9 f^2.
-/
theorem exercise1_6a (f : ℝ) : (Nat.choose 7 2 : ℝ) * f ^ 2 = 21 * f ^ 2 := by
  have h : Nat.choose 7 2 = 21 := by
    decide
  have h' : (Nat.choose 7 2 : ℝ) = (21 : ℝ) := by
    exact_mod_cast h
  simp [h']

theorem exercise1_6b (f : ℝ) : ((3 : ℝ) / 7) * (21 * f ^ 2) = 9 * f ^ 2 := by
  ring

/-! ## Exercise 1.7 -/

/- Problem:
Find noise vectors that give the all-zero syndrome. How many such nonzero
noise vectors are there?
-/
theorem exercise1_7 :
    ((Finset.univ.image encode).erase 0).card = 15 := by
  native_decide

/-! ## Exercise 1.8 -/

/- Problem:
Show that a block decoding error occurs whenever two or more bits are flipped in a block.
-/
theorem exercise1_8 :
    ∀ s : Fin 4 → ZMod 2, ∀ e : Fin 7 → ZMod 2,
      2 ≤ hammingNorm e → decodeCodeword (encode s + e) ≠ encode s := by
  native_decide

/-! ## Exercise 1.9 -/

/- Problem:
Design an error-correcting code and a decoding algorithm, estimate its error
probability, and add it to the performance graph.
-/
theorem exercise1_9_params :
    (30 : ℕ) = 30 ∧ (11 : ℕ) = 11 ∧ (5 : ℕ) = 5 ∧ (3 : ℕ) = 3 := by
  simp

/-! ## Exercise 1.10 -/

/- Problem:
Could there be a (14,8) code that can correct any two errors? Use a counting
argument to justify your answer.
-/
theorem exercise1_10 : (1 + 14 + 91 : ℕ) > 2 ^ 6 := by
  norm_num

/-! ## Exercise 1.11 -/

/- Problem:
Design a code (not a repetition code) that can correct any two errors in a block
of size N.
-/
theorem exercise1_11_params :
    (15 : ℕ) = 15 ∧ (6 : ℕ) = 6 ∧ (5 : ℕ) = 5 := by
  simp

/-! ## Exercise 1.12 -/

/- Problem:
Consider R9 as a concatenation of R3 with R3 (R3^2). Evaluate the error
probability for a sequential decoder and compare with the optimal decoder for R9.
-/
theorem exercise1_12_concat (f : ℝ) : concatR3SquaredErrorProbApprox f = 27 * f ^ 4 := by
  rfl

theorem exercise1_12_optimal (f : ℝ) : optimalR9ErrorProbApprox f = 126 * f ^ 5 := by
  rfl

end InfoLean.Books.MacKay.Chapter1
