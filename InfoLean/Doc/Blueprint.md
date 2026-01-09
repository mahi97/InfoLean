# InfoLean Blueprint

Status legend: todo / wip / done.

## Foundations
- [done] Basics/Prelude.lean: shared imports and notation
- [done] Basics/FiniteProb.lean: PMF toReal bounds
- [done] Basics/LogLemmas.lean: negMulLog nonneg helper
- [done] Entropy/Basic.lean: finite entropy definition + nonnegativity
- [done] Examples/Bernoulli.lean: Bernoulli entropy definition + binEntropy bridge

## Finite entropy API
- [todo] entropy invariance under bijection
- [todo] entropy <= log card
- [todo] entropy of uniform PMF
- [done] conditional entropy (finite)
- [done] chain rule (finite)

## Mutual information
- [done] Entropy/MutualInformation.lean: mutualInformation definition + basic identity
- [todo] nonnegativity
- [todo] independence implies zero
- [todo] data processing (finite)

## Divergence
- [done] Divergence/KL.lean: re-export mathlib klDiv
- [todo] finite KL divergence for PMF
- [todo] Gibbs inequality for finite KL
- [todo] I(X;Y) = KL(p_xy || p_x_prod_p_y) finite

## Channels
- [done] Channels/Channel.lean: Channel alias
- [todo] channel composition lemma or notation
- [todo] data processing via kernels
