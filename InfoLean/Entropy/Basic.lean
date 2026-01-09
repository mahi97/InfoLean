import InfoLean.Basics.LogLemmas

namespace InfoLean

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Shannon entropy for a finite probability mass function, measured in nats. -/
noncomputable def entropy (p : PMF α) : ℝ := by
  classical
  exact ∑ a, Real.negMulLog (p a).toReal

lemma entropy_nonneg (p : PMF α) : 0 ≤ entropy p := by
  classical
  unfold entropy
  refine Finset.sum_nonneg ?_
  intro a ha
  exact negMulLog_pmf_nonneg p a

end InfoLean
