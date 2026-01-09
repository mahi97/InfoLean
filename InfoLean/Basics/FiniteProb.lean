import InfoLean.Basics.Prelude

namespace InfoLean

variable {α : Type*}

lemma pmf_toReal_nonneg (p : PMF α) (a : α) : 0 ≤ (p a).toReal := by
  exact ENNReal.toReal_nonneg

lemma pmf_toReal_le_one (p : PMF α) (a : α) : (p a).toReal ≤ 1 := by
  have hle : p a ≤ ENNReal.ofReal (1 : ℝ) := by
    simpa using (p.coe_le_one a)
  exact ENNReal.toReal_le_of_le_ofReal (by exact zero_le_one) hle

end InfoLean
