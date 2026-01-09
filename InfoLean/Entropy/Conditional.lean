import InfoLean.Entropy.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace InfoLean

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Conditional entropy `H(X|Y)` for a joint `PMF` on `α × β`, defined as `H(X,Y) - H(Y)`. -/
noncomputable def condEntropy (p : PMF (α × β)) : ℝ :=
  entropy p - entropy (p.map Prod.snd)

lemma chain_rule (p : PMF (α × β)) :
    entropy p = entropy (p.map Prod.snd) + condEntropy p := by
  simp [condEntropy]

end InfoLean
