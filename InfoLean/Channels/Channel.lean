import Mathlib.Probability.Kernel.Basic

namespace InfoLean

/-- A channel is a Markov kernel between measurable spaces. -/
abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  ProbabilityTheory.Kernel α β

end InfoLean
