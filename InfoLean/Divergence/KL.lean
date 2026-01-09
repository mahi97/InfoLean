import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace InfoLean

open MeasureTheory

noncomputable abbrev klDiv {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ENNReal :=
  InformationTheory.klDiv μ ν

end InfoLean
