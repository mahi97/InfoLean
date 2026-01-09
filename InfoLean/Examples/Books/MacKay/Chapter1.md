# Chapter 1: Introduction to Information Theory

Notes:
- Exercises and solutions listed here are extracted from Chapter 1 of the book.
- Solutions are only included when explicitly provided in the text.
- No additional derivations are added beyond the book's provided solutions.

## Exercise 1.1

Problem:
A bent coin with probability f of heads is tossed N times.
1) What is the distribution of the number of heads r?
2) What are the mean and variance of r?

Solution (as provided in the book):
- r has a binomial distribution:
  P(r | f, N) = (N choose r) * f^r * (1 - f)^(N - r)
- Mean:
  E[r] = N * f
- Variance:
  var[r] = N * f * (1 - f)

## Exercise 1.2

Problem:
Show that using the repetition code R3 reduces the error probability over a binary symmetric
channel with noise level f. Compute the decoded bit error probability.

Solution (as provided in the book):
- A decoding error occurs if two or more bits in a block of three are flipped.
- The decoded bit error probability is:
  p_b = C(3,2) * f^2 * (1 - f) + C(3,3) * f^3
- For f = 0.1:
  p_b = 3 * (0.1)^2 * (0.9) + (0.1)^3 = 0.027 + 0.001 = 0.028
  Rounded: p_b ~ 0.03

## Exercise 1.3

Problem:
(a) Show that for odd N, the decoded error probability of the repetition code R_N is:
    p_b = sum_{n=(N+1)/2}^{N} C(N,n) * f^n * (1 - f)^(N - n)
(b) For f = 0.1, identify the dominant term in the sum.
(c) Use Stirling's approximation to estimate the dominant term.
(d) For f = 0.1, find how large N must be to achieve p_b ~ 10^(-15).

Solution (as provided in the book):
- The dominant contribution comes from the smallest majority error term:
  n = (N + 1) / 2
- Stirling's approximation yields:
  C(N, N/2) ~ 2^N / sqrt(pi * N / 2)
- The probability decays exponentially in N.
- For f = 0.1, the required repetition length is approximately N ~ 61.
