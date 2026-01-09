import InfoLean.Entropy.Conditional

namespace InfoLean

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Mutual information `I(X;Y)` for a joint `PMF` on `α × β`. -/
noncomputable def mutualInformation (p : PMF (α × β)) : ℝ :=
  entropy (p.map Prod.fst) + entropy (p.map Prod.snd) - entropy p

lemma mutualInformation_eq_entropy_sub_condEntropy (p : PMF (α × β)) :
    mutualInformation p = entropy (p.map Prod.fst) - condEntropy p := by
  simp [mutualInformation, condEntropy, sub_eq_add_neg, add_left_comm, add_comm]

end InfoLean
