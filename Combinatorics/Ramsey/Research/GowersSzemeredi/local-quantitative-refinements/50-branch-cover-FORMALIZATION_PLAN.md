# Proposed formalization route

The article contains the complete mathematical proofs. The following is an implementation plan, not a claim that Lean code has been verified.

## A. Finite cover library

Define agreement of a finite function with a finite list of polynomial graphs. Prove that a nonconstant degree-d polynomial agrees with an R-valued word at at most dR points. Define the maximum mass of an s-element subset of the alphabet, avoiding order-statistic machinery initially. Prove the finite list envelope, exact optimum when the qth branch mass exceeds dR, and the optimizer deficit.

Lift the upper bound by summing over fibres. Then sum over a finite disjoint family of box carriers. Keep the last-coordinate degree hypothesis independent of the base dependence; this stronger statement makes the application particularly small.

## B. Balanced-word existence

Work on the finite uniform space of words `S^(ZMod p)`. Prove or reuse Bernoulli concentration and union-bound the progression/symbol events. The main counterexample needs only a uniform alphabet and a rational tolerance. First prove a conditional disproof given a balanced word; then discharge existence. The logarithmic threshold can be added last.

## C. Source witnesses

Use the full input set and full sidelength set, zero anchor, and all cube elements at every sidelength. `AxisCube` is a pair of base and side vectors, so a cube based at zero exists even at sidelength zero. Prove the good domain is the universe and the all-ones vertex map is `fun z => a (section16Last z)`.

Prove the identity-partition finite-range certificate for `MultiplyLinear`; include zero width. Prove the identity constant-line-cover certificate with distinct natural counts qGamma and qDelta. Apply these with qGamma = R and qDelta = 1.

## D. Negate the target

At loss 1/2 on the full proper two-box, extract the graph bound Q and width bound p^(1/Q). Restrict each multiaffine graph to the last variable, apply the finite cover library cellwise, and sum. Conclude the retained set has size at most 5*p^2/16, contradicting its lower bound p^2/2.

The eventual target is the negation of the pinned `lemma_16_10`. Do not overwrite its definition during the proof: retaining the original predicate makes the disproof auditable.

## E. Preserve a positive interface

The existing `section16_local_affine_lift` has an explicit count r*p0 + r^2*p0^2 and a separate width condition. Reuse that theorem with its parameters intact. Any absorption into a standard control function must be a separate proved statement, checked against the balanced finite-alphabet examples.

The endpoint full-domain product-property equivalence can be formalized independently through equality in the count of additive quadruples, affine coordinate restrictions, and induction on dimension. It clarifies why the negative theorem does not establish failure under that stronger upstream hypothesis.
