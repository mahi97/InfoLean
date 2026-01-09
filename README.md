# InfoLean

## Roadmap
- Milestone 0: foundations (shared imports, PMF helpers, finite entropy)
- Milestone 1: finite entropy API (invariance, bounds, uniform PMF)
- Milestone 2: conditional entropy and chain rule (finite)
- Milestone 3: mutual information (finite)
- Milestone 4: divergence and KL links
- Milestone 5: channels as kernels and data processing
- Milestone 6: measure-theoretic generalization (countable and general spaces)
- Milestone 7: coding theorems and asymptotics (later)

## Task list (live)
- [x] Replace template README with InfoLean scope and structure
- [x] Create core module layout under `InfoLean/`
- [x] Add finite entropy for `PMF` and prove nonnegativity
- [x] Add Bernoulli entropy example
- [x] Add Bernoulli entropy bridge to `Real.binEntropy`
- [x] Add KL divergence alias (mathlib re-export)
- [x] Add channel alias (Markov kernel)
- [ ] Add entropy invariance under bijection
- [ ] Add entropy upper bound by `log (Fintype.card)`
- [ ] Add uniform distribution entropy lemma
- [x] Define conditional entropy for `PMF`
- [x] Prove chain rule (finite)
- [ ] Define mutual information and basic identities
- [ ] Prove nonnegativity and independence implies zero
- [ ] Define finite KL divergence for `PMF` and relate to entropy
- [ ] Add `I(X;Y) = KL(p_xy || p_x_prod_p_y)` (finite)
- [ ] Add data processing inequality (kernel form)
- [ ] Expand to countable and general measurable spaces

## Goal
InfoLean is a Lean 4 library for information theory that builds on mathlib's probability and
measure theory stack. The initial focus is classical Shannon information theory for finite
alphabets, then extensions toward measure-theoretic definitions and kernel-based channel theory.

## Scope and policy
- Core target: finite entropy, conditional entropy, mutual information, and KL divergence.
- Postponed (planned later): coding theorems, rate-distortion, large deviations, and quantum IT.
- Log base: natural log (nats), consistent with mathlib.

## Repository layout
- `InfoLean/Basics/`: shared imports and helper lemmas (PMF bounds, log lemmas)
- `InfoLean/Entropy/`: entropy definitions and finite-case lemmas
- `InfoLean/Divergence/`: KL divergence wrappers and future finite KL
- `InfoLean/Channels/`: channels as Markov kernels
- `InfoLean/Examples/`: small worked examples
- `InfoLean/Doc/Blueprint.md`: theorem checklist and statuses
- `InfoLean/Mathlib/`: local patches or missing declarations for upstreaming

## Getting started
- Build: `lake build`
- Main umbrella file: `InfoLean.lean`

## Notes
- See `InfoLean/Doc/Blueprint.md` for the live theorem checklist and dependencies.
