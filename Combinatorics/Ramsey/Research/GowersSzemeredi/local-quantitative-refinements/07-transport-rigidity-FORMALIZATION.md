# Proposed Lean integration: obligations, not completed code

## Baseline

Repository: `VladimirReshetnikov/ProveIt`

Commit: `ae0e895748209f0dd079c6b5ca6df6c6fc065a81`

Directory: `Combinatorics/Ramsey/Lean/GowersSzemeredi/`

The existing source defines `lemma_10_9` in `Section10.lean`, and
`Proofs10Shift.lean` contains `lemma_10_9_holds`. This package does not modify
those declarations and includes no new compiled Lean file.

## Existing concepts to reuse

`MultifunctionDomain`, `MultifunctionDomain.fibre`,
`MultifunctionDomain.fibreSize`, `MultifunctionDomain.shift`,
`MultifunctionDomain.FibreSaturated`, `AlmostEvery`, `DomainInvariant`,
`IsSection10ShiftRegular`, `IsSection10LocalDifferenceModel`, and `FreimanHom`.

Read the definition of `FreimanHom` before choosing a tuple or multiset
interface. The paper's tuple-based definition is the mathematical target;
no API equivalence theorem has been compiled as part of this package.

## First target: factor-two order-k rigidity

Inputs, in mathematical notation:

- finite nonempty fiber-saturated W;
- symmetric B, with D subset B;
- R(u) <= 2 R(v) for all u,v in W;
- overlap at least (1-eta)|W| for every B-shift;
- 0 <= theta <= 1 and eta >= 0;
- for every d in D, the two-level local difference model with error theta;
- integer k >= 2;
- (4k-2)(2 theta - theta^2 + eta) < 1.

Output: `FreimanHom k D psi` (after selecting the appropriate exact API).

This target does not need the full transport-profile optimization. A direct
likelihood-ratio domination bound suffices. Derive order five under the
existing real-power smallness assumption only after proving this interface.

## Second target: retain ambient invariance

Additional inputs:

- lower fiber bound r0 > 0 on W;
- |R(g+d)-R(g)| <= L for all ambient g and all selected directions;
- tau = L/r0;
- [2k + tau k(k-1)](2 theta - theta^2 + eta) < 1.

Output: the same order-k conclusion. Here the global quantifier on g is
important: a prefix may pass through indices outside the usable support.

Substitute the Section 10 lower bound r0 = alpha^2 M/16 and L = sigma M.
The full hypotheses give tau <= eta*rho <= eta. This additional step must not
be silently folded into the weaker shift-regular assumptions.

## Finite counting route

1. Define the support S as the indices occurring in W. Prove its fibers are
   exactly the full ambient fibers for those indices.
2. Define mu(g) = R(g)/|W| on S and zero outside. A sum of rational weights or
   nonnegative real weights is adequate; a general measure library is not
   required for the first implementation.
3. Define boundary failure as one before branching into an internal target
   case. Denominator positivity follows from membership in S.
4. Define F_d(g) by the independently sampled pair in the two internal fibers.
   Prove the cancellation formula for the source-point law. Do not replace it
   by uniform counting of all index-related pairs.
5. Prove the nested-to-average inequality using an intersection count of good
   sources and internal destinations. Empty target fibers can be vacuously
   good in `AlmostEvery`; their source mass is nevertheless boundary failure.
6. Construct the finite product of formal path-position fibers, with two
   explicitly shared endpoint variables. Outside support, use a dummy type
   value and mark the first exit as failure.
7. For each edge, restrict only on earlier *indices* lying in S. This condition
   depends on the initial index and not on point-value samples. Bound the edge
   marginal by a translated source weight times F_d(g).
8. Apply the finite weighted union bound. A strictly positive successful mass
   implies a sample exists. Telescope both paths using the same endpoints.
9. Sum the prefix domination bounds. The first prefix costs delta, not
   2*delta. Subsequent prefixes cost at most 2*delta, not 2^j*delta.
10. For ambient invariance, compare a prefix directly with the initial law;
    telescoping yields 1+j*tau rather than repeated multiplicative losses.

## Edge cases that need their own test lemmas

- Empty D: every positive-order relation is vacuous.
- Nonempty D: a direction in B and nonempty W force eta >= 0 from overlap.
- eta = theta = 0: the averaged proof works without dividing by either.
- Zero direction: source and destination are independent samples from one
  fiber, not the same point.
- Total shift zero: the two endpoint random variables are still independent
  even though they lie in the same fiber.
- Repeated internal indices: keep distinct formal samples independent.
- Different path lengths: the proof allows any two positive lengths.
- Empty ambient destination: it is an exit from S, never a denominator.
- A path leaving and later reentering S: its first exit is already charged.
- Exact budget one: no strict conclusion; the cyclic winding family witnesses
  the necessity of strictness in the balanced uniform-defect theorem.

## Constant checks and audit

Use exact rational arithmetic for 71/1296, 23/144, 56/225 and the endpoint
budgets. Prove the monotonicity of q(theta)=2 theta-theta^2 on [0,1] once.
Isolate the real-power step relating theta=10 eta^(1/5) to eta bounds from the
rational polynomial algebra that follows it.

After actual implementation, run the repository build and the namespace
axiom audit. Record the exact toolchain, Mathlib version, command, exit status,
and new theorem names. A proposition-valued catalogue entry or an unexecuted
proof outline is not a successful formalization. None of these future actions
is represented as already performed in the present package.
