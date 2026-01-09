import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval

namespace InfoLean.Coding

open scoped BigOperators

/-- Majority-decoding error probability for repetition code `R_N` (odd `N`). -/
def repetitionErrorProb (N : ℕ) (f : ℝ) : ℝ :=
  Finset.sum (Finset.Icc ((N + 1) / 2) N) fun n =>
    (Nat.choose N n : ℝ) * f ^ n * (1 - f) ^ (N - n)

/-- Decoded bit error probability for repetition code `R3`. -/
def repetitionErrorProb3 (f : ℝ) : ℝ :=
  (Nat.choose 3 2 : ℝ) * f ^ 2 * (1 - f) + (Nat.choose 3 3 : ℝ) * f ^ 3

/-- Dominant term index for the repetition code approximation. -/
def repetitionDominantIndex (N : ℕ) : ℕ :=
  (N + 1) / 2

/-- Stirling-based approximation for the central binomial coefficient. -/
noncomputable def centralBinomApprox (N : ℕ) : ℝ :=
  (2 ^ N : ℝ) / Real.sqrt (Real.pi * ((N : ℝ) / 2))

/-- Approximate error probability for repetition codes (Stirling-based). -/
noncomputable def repetitionErrorProbApprox (N : ℕ) (f : ℝ) : ℝ :=
  (1 / Real.sqrt (Real.pi * ((N : ℝ) / 8))) * (4 * f * (1 - f)) ^ (N / 2)

/-- Approximate repetition length for `f = 0.1` and `p_b ~ 10^-15`. -/
def repetitionApproxN_f01 : ℕ :=
  61

def concatR3SquaredErrorProbApprox (f : ℝ) : ℝ :=
  27 * f ^ 4

def optimalR9ErrorProbApprox (f : ℝ) : ℝ :=
  126 * f ^ 5

end InfoLean.Coding
