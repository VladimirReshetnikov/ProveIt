# Recovering the terminal content bound in the tag interface

Status: **verified conditional component**, with **31 operations =
14 multiplications + 17 additions/subtractions**, ten Boolean fields, and ten
equality comparisons. This is a separate successor to the frozen, independently
verified 32-operation construction in
`EXPLORATION_SINGLE_PROJECTOR_TAG_HISTORY.md`.

The author, root, and independent affine reviewer each completed a full proof
and source review and a fresh complete verification run without findings.
The proof, checker, and receipt are frozen after these gates.

Delete its final instruction and comparison

    content_bound = Nfinal+alphaN,
    content_bound = Lfinal,

and delete the positive coordinate alphaN. Every other equation, mask, input
contract, geometry assumption, and domain is retained. In particular Nfinal
is still nonnegative, Lfinal is positive, and the two retained boundary sums
give Linit<A and Lfinal<K. The resulting certificate has the same conditional
encoded-word halting theorem as its predecessor. It is not a universal
Diophantine operation bound: Boolean-mask realization, power geometry, strictly
positive word adapters, and raw numerical input conversion remain uncounted.

## 1. A strict positive-remainder identity

Use the predecessor's fixed constants K=3^beta, Af=3^a, Khalf=K/3,
B=Af/3, and U, the Boolean ternary value of the nonempty appendant. Its fixed
padding choice gives R>K. Let d=3E+S1. The retained equations include

    L=M0+M1=2(N+Nbar)+H,
    R(N-d+U M1)=K(N-Ninit+q Nfinal),
    R(3M0+Af M1)=K(L-Linit+q Lfinal).                         (1)

The final equation is three times the actual divided length comparison; it
does not add an operation. Combining (1) gives the exact identity

    Kq(Lfinal-2Nfinal)
      = 2R M0 + R(Af-2U-1)M1
        + (R-K)H + 2(R-K)Nbar
        + K(Linit-2Ninit) + 2R d.                            (2)

Every summand on the right is nonnegative, and the sum is strictly positive.
Indeed, M0, M1, Nbar, E, and S1 are nonnegative. Also H>0 and R>K. Since u is
a binary word of length a,

    2U <= Af-1.

Since the specified input word is Boolean ternary of length ell,

    2Ninit <= Linit-1.

Thus (2) proves the stronger bound

    0 <= 2Nfinal < Lfinal.                                   (3)

This proof is global algebra on the retained equations. It does not decode
any row, assume that all rows are causal, or assume that Lfinal is already a
power of three. In particular, it also applies to arbitrary certificates with
a suffix after the first real halt.

For an exact source-level check, let F_N and F_L be the left-minus-right
residuals of the last two equations in (1), and put

    F_C=2(N+Nbar)+H-L,  F_S=M0+M1-L.

If P denotes the right side of (2), the unrestricted polynomial identity is

    Kq(Lfinal-2Nfinal)-P
      = 2F_N-F_L-(R-K)F_C+R F_S.                             (4)

The checker expands (4) symbolically, including its signs. F_L is precisely
three times the length-source residual under the fixed relations Af=3B and
K=3Khalf.

## 2. Exact extension and operation count

Every solution of the new system has the unique extension

    alphaN = Lfinal-Nfinal > 0.                              (5)

That extension satisfies the deleted comparison and hence every equation and
mask of the 32-operation predecessor. Conversely, forgetting alphaN from any
old solution satisfies the new system. All retained coordinates and registers
are unchanged. This is an exact two-way solution correspondence, not merely
an eventual-halting argument using the first genuine prefix.

The predecessor's full forward and reverse theorem therefore transfers
directly. The arithmetic change is exactly one deleted addition, one deleted
supplied positive coordinate, and one deleted equality comparison. The ten
Boolean fields remain

    Q, S0, S1, M0, M1, G, N, Nbar, E, Ebar.

The 29-operation transition-and-projector subtotal is unchanged; it now has
two paid boundary additions, giving 31=14M+17A. No extra operation is charged
for reconstructing a deleted coordinate in the mathematical equivalence proof.
The stronger bound (3) is proved, not supplied as an additional test.

## 3. Exact verification and its scope

The companion `explore_tag_terminal_bound_recovery.py` imports the frozen
32-operation schedule and removes exactly its last instruction and comparison.
It independently expands all ten retained source comparisons and the complete
identity (4). Its JSON receipt includes every one of the 31 instructions.

Fresh canonical checks construct all ten masks and evaluate the actual new
31-operation schedule for 944 observed halting histories containing 2,318
source rows. For every witness the checker independently evaluates (2),
reconstructs the positive alphaN, and runs all eleven predecessor comparisons.
The 428 inputs still active at the 20-step test cutoff remain unclassified.
The three-formal-row certificate whose real halt occurs after one step is
retained and receives the same exact extension checks.

The adversarial gate reruns the predecessor's seven complete finite
configurations, with every integer terminal length 1<=Lfinal<K. It enumerates
385,024 guarded-Q/head candidates, 28 accepted length words, and 2,688 full
content candidates. It solves Nfinal from the retained exact content equation
and **does not filter by any upper bound on Nfinal**. It imposes only the
retained nonnegative domain. The 30 accepted complete certificates all satisfy
the derived strict bound (3) and have an actual halting prefix. No additional
terminal solution was hidden by a predecessor-bound filter.

These finite checks corroborate the unrestricted positive-remainder proof;
they do not classify the cutoff computations or establish an implementation
of the external Boolean-mask, geometry, positivity, or raw-input contracts.
