# Sources, exact question, and attribution

Checked on September 20, 2026. The sources below are primary research papers.
The arXiv submission histories consulted displayed a first version dated
May 27, 2026 for each paper. The mathematical target in this report is explicitly
version-specific; a comprehensive priority determination has not been made.

## 1. Noncommutative infinitary semigroups

Paolo Lipparini, arXiv:2605.28413v1 [math.GR].

https://arxiv.org/abs/2605.28413v1
https://arxiv.org/html/2605.28413v1

Relevant locations:

- Definition 3.1: singleton axiom (U) and one-way regrouping axiom (N).
- Definition 3.8: extension preserves defined products but may add products
  and elements.
- Proposition 5.1: the known inverse obstruction involving an alternating
  omega-word and prescribed infinite identity powers.
- Definition 6.2: the complete-identity condition is stated as deletion from
  a word whose product is already defined.
- Remark 7.1(b): the general extension problem, the necessary pairwise
  condition (Eq), and the expectation that (Eq) is insufficient.

The report answers the last sufficiency issue with a two-element example.
It does not claim to solve the entire extension-classification problem.

The displayed (Eq) statement calls the maps surjective without repeating the
order-preserving qualification used for ordered regrouping. The report uses
convex partitions for general ordered statements. Its main C2 example also
satisfies the stronger arbitrary-surjection interpretation, so this distinction
does not affect the counterexample.

The nonextension mechanism itself is not new: it is explicitly credited to
Proposition 5.1. The proof that the proposed partial domain satisfies every
instance of (Eq), and the resulting application to the stated question, are
what the report develops.

## 2. One-sided inverses in noncommutative infinitary semigroups

Paolo Lipparini, arXiv:2605.28416v1 [math.GR].

https://arxiv.org/abs/2605.28416v1
https://arxiv.org/html/2605.28416v1

Used to distinguish one-sided inverses from the bilateral unit obstruction.
The paper constructs a complete noncommutative infinitary semigroup with a
complete identity and nontrivial one-sided inverses. This prevents an
unjustified generalization from directly finite monoids to all monoids.

## 3. Ordinal semigroups

Paolo Lipparini, arXiv:2605.28419v1 [math.LO].

https://arxiv.org/abs/2605.28419v1
https://arxiv.org/html/2605.28419v1

Used to compare the counterexample with a positive extension theorem whose
premise already includes every product through a specified infinite ordinal.
In particular, a system with every finite and omega product can be expanded to
all countable ordinal products. The two-element example does not satisfy that
premise: it proves that the missing a^omega product cannot be added consistently.

## Research status

The article supplies conventional proofs, not just plausible constructions or
experimental evidence. The program provides exact finite and symbolic checks.
No outside referee or proof assistant has certified the full report. Searches
did not establish a later resolution or prior occurrence of these exact
constructions; this is not evidence of exhaustive coverage or a priority claim.
