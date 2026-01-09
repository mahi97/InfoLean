import InfoLean.Entropy.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace InfoLean

lemma bernoulliEntropy_nonneg (p : NNReal) (hp : p ≤ 1) :
    0 ≤ entropy (PMF.bernoulli p hp) := by
  simpa using (entropy_nonneg (p := PMF.bernoulli p hp))

lemma bernoulliEntropy_eq_binEntropy (p : NNReal) (hp : p ≤ 1) :
    entropy (PMF.bernoulli p hp) = Real.binEntropy (p : ℝ) := by
  classical
  have hsum :
      entropy (PMF.bernoulli p hp) =
        Real.negMulLog (p : ℝ) + Real.negMulLog ((1 - p : NNReal) : ℝ) := by
    simp [entropy, PMF.bernoulli_apply]
  calc
    entropy (PMF.bernoulli p hp) =
        Real.negMulLog (p : ℝ) + Real.negMulLog ((1 - p : NNReal) : ℝ) := hsum
    _ = Real.negMulLog (p : ℝ) + Real.negMulLog (1 - (p : ℝ)) := by
        simp [NNReal.coe_sub hp]
    _ = Real.binEntropy (p : ℝ) := by
        simpa using (Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (p : ℝ)).symm

end InfoLean
