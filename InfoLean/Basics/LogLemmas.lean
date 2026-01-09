import InfoLean.Basics.FiniteProb

namespace InfoLean

variable {α : Type*}

lemma negMulLog_pmf_nonneg (p : PMF α) (a : α) : 0 ≤ Real.negMulLog (p a).toReal := by
  exact Real.negMulLog_nonneg (pmf_toReal_nonneg p a) (pmf_toReal_le_one p a)

end InfoLean
