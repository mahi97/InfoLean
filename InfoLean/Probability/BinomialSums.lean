import InfoLean.Basics.FiniteProb
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace InfoLean

open scoped BigOperators

def binomialMeanSum (N : ℕ) (f : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun k =>
    (k : ℝ) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)

def binomialFalling2Sum (N : ℕ) (f : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun k =>
    (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)

def binomialSecondMomentSum (N : ℕ) (f : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun k =>
    ((k : ℝ) ^ 2) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)

def binomialVarianceSum (N : ℕ) (f : ℝ) : ℝ :=
  binomialSecondMomentSum N f - (binomialMeanSum N f) ^ 2

lemma binomialMeanSum_zero (f : ℝ) : binomialMeanSum 0 f = 0 := by
  simp [binomialMeanSum]

lemma binomialMeanSum_succ (N : ℕ) (f : ℝ) :
    binomialMeanSum (N + 1) f = (N + 1 : ℝ) * f := by
  classical
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun k =>
        (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) =
        (f + (1 - f)) ^ N := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (add_pow f (1 - f) N).symm
  calc
    binomialMeanSum (N + 1) f =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          (k + 1 : ℝ) * (Nat.choose (N + 1) (k + 1) : ℝ) *
            f ^ (k + 1) * (1 - f) ^ (N - k)) := by
          simp [binomialMeanSum, Finset.sum_range_succ', pow_succ, mul_comm, mul_left_comm,
            mul_assoc]
    _ = Finset.sum (Finset.range (N + 1)) (fun k =>
          (N + 1 : ℝ) * (Nat.choose N k : ℝ) * f ^ (k + 1) * (1 - f) ^ (N - k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hchoose :
              (Nat.choose (N + 1) (k + 1) : ℝ) * (k + 1 : ℝ) =
                (N + 1 : ℝ) * (Nat.choose N k : ℝ) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq N k).symm
          calc
            (k + 1 : ℝ) * (Nat.choose (N + 1) (k + 1) : ℝ) *
                f ^ (k + 1) * (1 - f) ^ (N - k) =
              (Nat.choose (N + 1) (k + 1) : ℝ) * (k + 1 : ℝ) *
                f ^ (k + 1) * (1 - f) ^ (N - k) := by
              ring
            _ = (N + 1 : ℝ) * (Nat.choose N k : ℝ) *
                f ^ (k + 1) * (1 - f) ^ (N - k) := by
              simp [hchoose, mul_comm, mul_left_comm, mul_assoc]
    _ = (N + 1 : ℝ) * f *
          Finset.sum (Finset.range (N + 1)) (fun k =>
            (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) := by
          simp [pow_succ, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    _ = (N + 1 : ℝ) * f := by
          simp [hsum]

lemma binomialMeanSum_eq (N : ℕ) (f : ℝ) : binomialMeanSum N f = (N : ℝ) * f := by
  cases N with
  | zero =>
      simp [binomialMeanSum]
  | succ N =>
      simpa using binomialMeanSum_succ N f

lemma binomialFalling2Sum_zero (f : ℝ) : binomialFalling2Sum 0 f = 0 := by
  simp [binomialFalling2Sum]

lemma binomialFalling2Sum_succ_succ (N : ℕ) (f : ℝ) :
    binomialFalling2Sum (N + 2) f = (N + 2 : ℝ) * (N + 1 : ℝ) * f ^ 2 := by
  classical
  let term : ℕ → ℝ := fun k =>
    (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (Nat.choose (N + 2) k : ℝ) * f ^ k *
      (1 - f) ^ ((N + 2) - k)
  have hterm0 : term 0 = 0 := by
    simp [term]
  have hterm1 : term 1 = 0 := by
    simp [term]
  have hshift :
      binomialFalling2Sum (N + 2) f =
        Finset.sum (Finset.range (N + 1)) (fun k => term (k + 2)) := by
    unfold binomialFalling2Sum
    conv_lhs => simp [term]
    rw [Finset.sum_range_succ' term (N + 2)]
    rw [Finset.sum_range_succ' (fun k => term (k + 1)) (N + 1)]
    simp [hterm0, hterm1, add_left_comm, add_comm]
  have hterm_simpl (k : ℕ) :
      term (k + 2) =
        (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) *
          f ^ (k + 2) * (1 - f) ^ (N - k) := by
    simp [term, Nat.add_sub_add_right]
  have hshift' :
      binomialFalling2Sum (N + 2) f =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) *
            f ^ (k + 2) * (1 - f) ^ (N - k)) := by
    refine hshift.trans ?_
    refine Finset.sum_congr rfl ?_
    intro k hk
    simpa using hterm_simpl k
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun k =>
        (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) =
        (f + (1 - f)) ^ N := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (add_pow f (1 - f) N).symm
  calc
    binomialFalling2Sum (N + 2) f =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) *
            f ^ (k + 2) * (1 - f) ^ (N - k)) := by
          simpa using hshift'
    _ = Finset.sum (Finset.range (N + 1)) (fun k =>
          (N + 2 : ℝ) * (N + 1 : ℝ) * (Nat.choose N k : ℝ) *
            f ^ (k + 2) * (1 - f) ^ (N - k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have h1 : (Nat.choose (N + 2) (k + 2) : ℝ) * (k + 2 : ℝ) =
              (N + 2 : ℝ) * (Nat.choose (N + 1) (k + 1) : ℝ) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq (N + 1) (k + 1)).symm
          have h2 : (Nat.choose (N + 1) (k + 1) : ℝ) * (k + 1 : ℝ) =
              (N + 1 : ℝ) * (Nat.choose N k : ℝ) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq N k).symm
          have h12 :
              (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) =
                (N + 2 : ℝ) * (N + 1 : ℝ) * (Nat.choose N k : ℝ) := by
            calc
              (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) =
                  (k + 1 : ℝ) * ((k + 2 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ)) := by
                ring
              _ = (k + 1 : ℝ) * ((N + 2 : ℝ) * (Nat.choose (N + 1) (k + 1) : ℝ)) := by
                simp [h1, mul_comm, mul_left_comm]
              _ = (N + 2 : ℝ) * ((k + 1 : ℝ) * (Nat.choose (N + 1) (k + 1) : ℝ)) := by
                ring
              _ = (N + 2 : ℝ) * ((N + 1 : ℝ) * (Nat.choose N k : ℝ)) := by
                simp [h2, mul_comm, mul_assoc]
              _ = (N + 2 : ℝ) * (N + 1 : ℝ) * (Nat.choose N k : ℝ) := by
                ring
          calc
            (k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ) *
                f ^ (k + 2) * (1 - f) ^ (N - k) =
              ((k + 2 : ℝ) * (k + 1 : ℝ) * (Nat.choose (N + 2) (k + 2) : ℝ)) *
                (f ^ (k + 2) * (1 - f) ^ (N - k)) := by
              ring
            _ = ((N + 2 : ℝ) * (N + 1 : ℝ) * (Nat.choose N k : ℝ)) *
                (f ^ (k + 2) * (1 - f) ^ (N - k)) := by
              simp [h12]
            _ = (N + 2 : ℝ) * (N + 1 : ℝ) * (Nat.choose N k : ℝ) *
                f ^ (k + 2) * (1 - f) ^ (N - k) := by
              ring
    _ = (N + 2 : ℝ) * (N + 1 : ℝ) * f ^ 2 *
          Finset.sum (Finset.range (N + 1)) (fun k =>
            (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) := by
          simp [pow_succ, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    _ = (N + 2 : ℝ) * (N + 1 : ℝ) * f ^ 2 := by
          simp [hsum]

lemma binomialSecondMomentSum_eq (N : ℕ) (f : ℝ) :
    binomialSecondMomentSum N f = binomialFalling2Sum N f + binomialMeanSum N f := by
  classical
  unfold binomialSecondMomentSum binomialFalling2Sum binomialMeanSum
  have hrewrite :
      Finset.sum (Finset.range (N + 1)) (fun k =>
        ((k : ℝ) ^ 2) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          ((k : ℝ) * ((k - 1 : ℕ) : ℝ) + (k : ℝ)) * (Nat.choose N k : ℝ) *
            f ^ k * (1 - f) ^ (N - k)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    cases k with
    | zero =>
        simp
    | succ k =>
        simp [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    Finset.sum (Finset.range (N + 1)) (fun k =>
        ((k : ℝ) ^ 2) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          ((k : ℝ) * ((k - 1 : ℕ) : ℝ) + (k : ℝ)) * (Nat.choose N k : ℝ) *
            f ^ k * (1 - f) ^ (N - k)) := hrewrite
    _ =
        Finset.sum (Finset.range (N + 1)) (fun k =>
          (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (Nat.choose N k : ℝ) * f ^ k *
            (1 - f) ^ (N - k)) +
        Finset.sum (Finset.range (N + 1)) (fun k =>
          (k : ℝ) * (Nat.choose N k : ℝ) * f ^ k * (1 - f) ^ (N - k)) := by
        simp [Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

lemma binomialVarianceSum_eq (N : ℕ) (f : ℝ) :
    binomialVarianceSum (N + 2) f =
      (N + 2 : ℝ) * f * (1 - f) := by
  have hmean : binomialMeanSum (N + 2) f = (N + 2 : ℝ) * f := by
    simpa using binomialMeanSum_eq (N + 2) f
  have hfall : binomialFalling2Sum (N + 2) f = (N + 2 : ℝ) * (N + 1 : ℝ) * f ^ 2 := by
    simpa using binomialFalling2Sum_succ_succ N f
  have hsecond : binomialSecondMomentSum (N + 2) f =
      binomialFalling2Sum (N + 2) f + binomialMeanSum (N + 2) f := by
    simpa using binomialSecondMomentSum_eq (N + 2) f
  unfold binomialVarianceSum
  calc
    binomialSecondMomentSum (N + 2) f - (binomialMeanSum (N + 2) f) ^ 2 =
        (binomialFalling2Sum (N + 2) f + binomialMeanSum (N + 2) f) -
          (binomialMeanSum (N + 2) f) ^ 2 := by
        simp [hsecond]
    _ = (N + 2 : ℝ) * f * (1 - f) := by
        simp [hmean, hfall]
        ring

lemma binomialVarianceSum_eq_all (N : ℕ) (f : ℝ) :
    binomialVarianceSum N f = (N : ℝ) * f * (1 - f) := by
  cases N with
  | zero =>
      simp [binomialVarianceSum, binomialMeanSum, binomialSecondMomentSum]
  | succ N =>
      cases N with
      | zero =>
          have hmean : binomialMeanSum 1 f = (1 : ℝ) * f := by
            simpa using binomialMeanSum_eq 1 f
          have hsecond : binomialSecondMomentSum 1 f =
              binomialFalling2Sum 1 f + binomialMeanSum 1 f := by
            simpa using binomialSecondMomentSum_eq 1 f
          have hfall : binomialFalling2Sum 1 f = 0 := by
            simp [binomialFalling2Sum, Finset.sum_range_succ]
          unfold binomialVarianceSum
          simp [hmean, hsecond, hfall]
          ring
      | succ N =>
          simpa [Nat.add_assoc] using binomialVarianceSum_eq N f

lemma binomialExpectation_eq_sum (f : NNReal) (hf : f ≤ 1) (N : ℕ) :
    pmfExpectation (PMF.binomial f hf N) (fun i => (i : ℝ)) = binomialMeanSum N (f : ℝ) := by
  classical
  unfold pmfExpectation
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < N + 1 := by
    simpa [Finset.mem_range] using hi
  simp [PMF.binomial_apply, hi', mul_comm, mul_left_comm, mul_assoc, hf]

lemma binomialSecondMoment_eq_sum (f : NNReal) (hf : f ≤ 1) (N : ℕ) :
    pmfExpectation (PMF.binomial f hf N) (fun i => (i : ℝ) ^ 2) =
      binomialSecondMomentSum N (f : ℝ) := by
  classical
  unfold pmfExpectation
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < N + 1 := by
    simpa [Finset.mem_range] using hi
  simp [PMF.binomial_apply, hi', mul_comm, mul_left_comm, mul_assoc, pow_two, hf]

lemma binomialVariance_eq_sum (f : NNReal) (hf : f ≤ 1) (N : ℕ) :
    pmfVariance (PMF.binomial f hf N) (fun i => (i : ℝ)) = binomialVarianceSum N (f : ℝ) := by
  classical
  unfold pmfVariance binomialVarianceSum
  have hmean := binomialExpectation_eq_sum f hf N
  have hsecond := binomialSecondMoment_eq_sum f hf N
  simp [hmean, hsecond]

end InfoLean
