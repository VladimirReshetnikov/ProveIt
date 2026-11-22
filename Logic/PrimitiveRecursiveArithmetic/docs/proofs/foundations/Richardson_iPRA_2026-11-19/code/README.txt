RICHARDSON REDUCTION: EXACT RATIONAL DEMONSTRATIONS
=================================================

Requirements: Python 3.10 or later; standard library only.

Examples:

  python3 richardson.py demo --output demo_results.json
  python3 richardson.py evaluate examples/linear_root.json \
      --x 1.11415714087193 --bits 48
  python3 richardson.py compile examples/linear_root.json \
      --output examples/linear_root_expression.json
  python3 test_certificates.py

WHAT THIS CODE DOES

For a supplied integer-coefficient polynomial P in n natural variables, it
constructs a legal univariate elementary-expression abstract syntax tree:

  h_j(t) = t sin(t^(2j-1)),        u_j(t) = h_j(t)^2,
  C = max(1, sum of absolute coefficients),
  D = max(1, total degree),
  R(u) = 1 + sum u_j^2,
  L(u) = C D (2 R(u))^D,
  F(u) = 4 [ P(u)^2 + L(u)^2 sum sin(pi u_j)^2 ] - 1,
  E(t) = |F(u(t))| - F(u(t)).

The compiler uses only rational constants, pi, t, addition, multiplication,
sine, and absolute value. Integer powers are finite multiplication trees.
An expression DAG retains repeated subexpressions; unfolding it gives the
ordinary expression tree. The compiler does not import exp or log(2), since
the reduction lies in a smaller sublanguage of Richardson's language.

The companion report proves the global reduction. This program only builds
the expressions and produces finite interval certificates at selected
rational inputs. It is not a global identity decision procedure. It does
not implement a universal MRDP compiler and contains no fixed universal
Diophantine polynomial for machine halting.

INTERVAL CERTIFICATES

Every interval endpoint is a fractions.Fraction. Addition and multiplication
use exact rational interval arithmetic, followed by outward dyadic rounding.
Absolute value uses the exact image interval. No binary floating-point
number participates in a certificate.

Pi is enclosed by Machin's identity

  pi = 16 atan(1/5) - 4 atan(1/239).

Each arctangent is bounded between adjacent alternating partial sums. All
iterations are explicitly bounded. Sine uses its rational Taylor sums:
after summing M terms, let a be the first omitted absolute term. Once the
ratio of successive omitted terms is <= 1/2, the tail is bounded by 2a.
The loop has the explicit bound R^2 + R + work_bits + 8, where R is at least
one and at least the absolute argument. The elementary factorial estimate
in the report ensures that this bound suffices. For an input interval, the
one-Lipschitz bound for sine expands the midpoint enclosure by its radius.
The result is intersected with [-1,1].

The exact certification of these methods rests on the mathematical series,
Machin, and Lipschitz lemmas in the report; Python is not a proof assistant.

A PRIORI PRECISION CHOICE

With delta=2^(-work_bits), magnitude_and_width computes bounds B and W at
each node. Provided W_root delta <= 1, the true node magnitude is <= B, and
the returned interval has width <= W delta. This follows by induction on
the expression table. The recurrences are:

  rational or variable: B = ceil(abs(value))+1, W = 1;
  pi: B = 4, W = 3;
  addition: B = B1+B2, W = W1+W2+2;
  multiplication: B = B1 B2,
      W = (B1+1) W2 + (B2+1) W1 + 2;
  sine: B = 1, W = W_child+3;
  absolute value: B = B_child, W = W_child+2.

The extra 2 covers outward rounding at both endpoints. The sine series
error and pi series error fit the displayed spare constants. All parent
W values dominate their children's. The chosen working precision

  work_bits = target_bits + bit_length(W_root) + 2

therefore yields a final interval width <= 2^(-target_bits), with room to
spare. This is a finite predetermined precision, not an unbounded search.
The code checks this final width as an additional implementation check.

The final identity has the form |v|-v. Evaluating v once and applying the
exact monotone image interval max(0,-2v) preserves dependence and is often
tighter than independently subtracting two copies of v's interval. Both
the generic interval and this tighter interval are recorded in each JSON
certificate. A strictly positive lower endpoint certifies nonzero at that
one rational input. An interval equal to [0,0] at one input says nothing by
itself about values at other inputs.

EXAMPLES AND LIMITATIONS

linear_root.json has the natural root z=1. The supplied rational input
111415714087193/100000000000000 approximately satisfies t sin(t)=1. The
actual rigorous certificate comes from the rational enclosure, not from
that approximation statement.

linear_no_natural_root.json has a negative integer root but no natural
root. This checks the importance of the nonnegative u_j=h_j^2 substitution.
quadratic_no_root.json has no real root. zero_polynomial.json is identically
zero as a polynomial but compiles to a nonzero elementary expression, as
the reduction requires: its polynomial equation has natural solutions.

All test claims concern code behavior or individual rational enclosures.
The tests do not prove density, the gap lemma, MRDP, or the undecidability
theorem. No unavailable formal proof is represented as completed.
