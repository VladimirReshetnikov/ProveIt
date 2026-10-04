# Independent review of the integral first-row target floor

**PASS, with no requested author change.** I read the entire frozen
[proof](matrix193_integral_target_floor.md),
[helper](matrix193_integral_target_floor.py) and
[receipt](matrix193_integral_target_floor.json). The result is correct in
its stated model: three generic target gates are necessary and sufficient
after an integral unimodular basis change that preserves first-row
injectivity on the entire inherited twenty-letter group. It is not a
lower bound for a smaller set of actual positive semigroup products or
for a complete Diophantine representation.

| Frozen author file | SHA256 |
|---|---|
| matrix193_integral_target_floor.py | `47e726064a68e520835370827618a80ae4c460c52826e52846901b18a15040bd` |
| matrix193_integral_target_floor.json | `3d2bab17b0058311ea43162e4d6f6bae3a29d65b6f5034c2934d1167cd407a84` |
| matrix193_integral_target_floor.md | `ffbc7ec62eadaa323448b567722d1b8c0def4c5bd470eece020b53ed9bd42f30` |

## Group and integral-frame reduction

I independently read the actual tape matrices from the pinned
[Gamma1 receipt](matrix193_gamma1_recode.json), without importing its
source. They give T and U in H and reproduce

    W0=[[-29,3],[-10,1]],
    U^-1 W0 U=[[-14,3],[65,-14]]=W1,
    D=W1+14I=[[0,3],[65,0]],  D²=195I.

Because U belongs to H, the change from the original H' frame to this
normal frame carries the group to H itself. Composition with this fixed
integral unimodular matrix gives a bijection of all allowed basis changes;
the reduction does not restrict the frames being classified.

For an equal-diagonal frame S, the two off-diagonal entries multiply to
195. If its lower entry is c>0 and the first column is (p,r), then the
second column is forced to be (3r/c,65p/c), and

    65p²−3r²=c det(S).

I independently recomputed all fourteen forbidden residue images using
sets of square residues. The complete divisor/sign inventory leaves only
the values −3 and 65, without any bound on p or r. The resulting matrices
are respectively C J and C, where

    C=[[z,3h],[65h,z]],  z²−195h²=1.

Allowing negative c appends diag(1,−1), so it introduces no missing class.
The note's Pell descent is sufficient: for a positive norm-one unit
lambda>1 in Z[sqrt(195)], integer coefficients force lambda to be at
least epsilon=14+sqrt(195). Multiplying repeatedly by epsilon^-1 yields
a norm-one unit in [1,epsilon), hence 1. Thus all such units are signed
integral powers of epsilon, including inverses. Since 14I+D=−W1^-1,
every C belongs to ±H and conjugation by C leaves H unchanged.

The four remaining frame types therefore contain a nontrivial lower
unipotent obtained from U or from J^-1 T J. This gives an actual collision
with the identity under the first-row map in each case. The argument
uses the full group, rather than claiming that each colliding element
must also occur in the smaller accepted positive-product set.

## The two-gate cases and the shear

For S^-1 D S=[[u,v],[w,−u]], the integer v cannot vanish because
u²+vw=195. The target is

    (chi+28u psi, 28v psi).

When u=0 the first output is a wire, but the integral-frame result already
shows loss of the required group-wide injection. If u is nonzero, both
outputs need gates. From only independent chi,psi and fixed integer
constants, a single gate cannot produce chi+28u psi: an addition/subtraction
retaining chi with coefficient one gives a psi coefficient at most one
in magnitude, and multiplication
cannot produce these two distinct linear terms. Consequently any
two-gate circuit must first output 28v psi and then add it to, or
subtract it from, chi. This forces u=±v. A nonlinear first gate is not
a missing case: with two nontrivial outputs, that first gate must itself
be the linear second output.

For u=±v, the lower shear L=[[1,0],[−u/v,1]] is integral unimodular and

    L^-1 [[u,v],[w,−u]] L = [[0,v],[195/v,0]].

This shear preserves first-row injectivity exactly: the first row after
conjugation is the old first row multiplied by the invertible matrix L.
It therefore reduces either shared-product two-gate possibility to an
excluded equal-diagonal frame. The existing three-gate expression in
the inherited injective H' frame attains the resulting lower bound.

This gate proof counts multiplication by every fixed integer, including
negative integers, as a gate. It assumes polynomial identities in
independent chi and psi; it does not simplify only on indexed Pell
values or use other previously paid registers.

## Executable checks and retained scope

All three parent pins in the author helper match the installed frozen
Gamma1 files:

| Parent file | SHA256 |
|---|---|
| matrix193_gamma1_recode.py | `ae24e64539b450fd9c4db0b3e04ce440d00562dcfe532a43002d7c52da34757c` |
| matrix193_gamma1_recode.json | `9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668` |
| matrix193_gamma1_recode.md | `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742` |

My fresh data-only calculations independently reconstructed the actual
tape and normal-frame matrices and the fourteen residue exclusions.
Sequential Pell recurrences supplied 104 signed centralizer/frame
collision checks. Direct matrix multiplication checked 32 lower-shear
instances, covering both signs of every divisor v of 195 and both
choices u=±v. These bounded examples supplement the unrestricted
classification and shear proofs above; no bounded search is being
presented as a classification theorem.

Fresh exact author receipt replays from `/` passed under both normal
Python and `python3 -O`. The helper uses explicit exception checks,
authenticates the three parent files, rejects duplicate/nonfinite JSON
values and compares receipt types recursively. Its declared 68 collision
fixtures and 21 indexed-power checks agree with its literal loops and
receipt. No predecessor script or archived executable was run. I did
not re-enumerate the entire twenty-letter free-basis construction or
the 193-generator predecessor; those are inherited authenticated results.

The note correctly leaves rational changes of basis, different projected
coordinates, extra paid inputs, changed representations, identities
restricted to Pell points, and smaller positive-product sets outside this
bound. In particular, the exact Pell index and an unbounded membership
certificate remain unpaid, and no universal operation count changes.
