import InfoLean.Basics.Prelude

namespace InfoLean

open scoped BigOperators

variable {α : Type*}

lemma pmf_toReal_nonneg (p : PMF α) (a : α) : 0 ≤ (p a).toReal := by
  exact ENNReal.toReal_nonneg

lemma pmf_toReal_le_one (p : PMF α) (a : α) : (p a).toReal ≤ 1 := by
  have hle : p a ≤ ENNReal.ofReal (1 : ℝ) := by
    simpa using (p.coe_le_one a)
  exact ENNReal.toReal_le_of_le_ofReal (by exact zero_le_one) hle

/-! ### Finite expectation and variance -/

noncomputable def pmfExpectation {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

noncomputable def pmfVariance {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  pmfExpectation p (fun a => (f a) ^ 2) - (pmfExpectation p f) ^ 2

end InfoLean
