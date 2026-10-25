# Independent ordinary review of the window review

Reviewed by intake_e13 on 24 October 2026. The entire 251-line
`research/one-word-window-review/REVIEW.md` was read independently, together
with its source pins, the exact historical brief, the current brief and
their complete diff. **No mathematical finding.** This approves the stated
ordinary obstructions and local lemmas; it supplies no nine-positive source,
compiler, equation, operation census or formalization.

The reviewed REVIEW SHA256 is
`a0c330f0525be8c0da98b75b36080a1027daa04699b6261194c757e3820eb331`.
Its SOURCE_PINS SHA256 is
`16d46d0f1fbf69bf5d0dfe8ee210a6589e59d5d94b2cb7d2a38d11a40fce3941`.
All thirteen supporting whole-file pins authenticate. The historical brief
snapshot has SHA256
`3275ac4570aac12d2fb2a26c8fa7d5543424dfc37e984bbbfa8cf10754dd81c4`
and is byte-identical to the specified Git blob at
`76f2647cdf1c91b38e4c30d75fb791f0ff918b5e`. The corrected active brief
read here has SHA256
`2249ff7298d1c2b8871a8b33033a404cb978f501cce3058fdb53695d25e101ea`.

## Mask-budget arguments

For `Q=2^u,M=Q-1`, the alpha=1 argument is correct for all the stated
finite words. From `F=M-C`, the mask on b implies every common set bit
of a and b is a set bit of C. The mask on a excludes set bits of C-1.
Exactly one set bit of C is absent from C-1, the least significant set
bit of C. Thus the common population is at most one, and the union is a
u-bit word. The resulting bound `pc(a)+pc(b)<=u+1` uses no parity or
carry-free premise. It remains valid on the larger field allowing F=0.

The retained native interface instead gives population u+2 for the actual
two repeated masks. Incrementing the even low mask adds one bit;
decrementing the high mask, which has exactly two trailing zero bits,
also adds one. The native four-block saturation supplies the two mask
conditions without assuming carry-free rank blocks. Hence the alpha=1
lane is inconsistent before transport is used, under precisely that
retained interface. Changing K or tile coefficients alone cannot remove
this contradiction. It is not a nonexistence theorem for every one-word
compiler or for the underlying refutation problem.

The generalization is also valid. Put A=C-1. The identity
`A+alpha=M-F` bounds the final sum inside the same u-bit field. Each
single-power-of-two addition creates at most one bit absent immediately
before it. Every bit in the final sum absent from the original A must
have been created by one of these additions. Adding the distinct set
bits of alpha therefore bounds their number by `pc(alpha)`. The common
mask population is at most this number, so the required u+2 population
forces `pc(alpha)>=2`. This is necessary, not sufficient. The separate
low-two-bit argument correctly gives alpha=3 modulo4 in the unchanged
literal window, excluding both alpha=1 and alpha=J there.

## Transport algebra and the selective gap

With `P=K0+B^h`, transport gives `P*C=F modM`. If alpha=A(J) is fixed
independently of both word variables, the two derived congruences are

    (P+1)C = 1-A(J) modM,
    (P+1)F = P*(1-A(J)) modM.

Their nonempty solution sets are cosets of the indicated subgroup. A tie
depending on a word need not be linear: alpha=F^2 gives the displayed
quadratic congruence. The explicit q=32,P=5,digit-wise example has exactly
the four listed residues; neither that set nor its three positive examples
is a coset in the prime-order group. It is correctly presented only as a
counterexample to an overbroad linearization claim, not as a native compiler.

The repetend and remainder evolution statements hold. The correction to
the possible hidden-state size follows from `g<=B^h+K0+1<2B^h`, and a
proper divisor under the stated strict bound is smaller than B^h. Even
injective digit observations need not be Boolean-linear maps. The review
therefore does not infer nonuniversality merely from linear modular
remainder evolution or from the machine's nonlinear rule table.

For the local gap construction, A is the disjoint union of b outside a
and any Z outside both masks. Alpha is their intersection. Consequently
`A+alpha=b OR Z` without carries, `A AND a=0`, and
`F=M-(A+alpha)` is disjoint from b. Setting C=A+1 gives the desired field
sum. The native population budget guarantees at least two intersecting
bits. A bit of a outside b cannot be filled by Z, and therefore makes
F positive. These are local field/mask facts, not transport completeness.

The literal intersection formula is correct. Only the lowest radix digit
changes under the increment and decrement. Its intersection changes by
`3-4*epsilon`, with epsilon the bit2 of MC. Thus the whole intersection
is `D*J+3-4*epsilon`, D=MC AND MF_native. For the actual compact44 and
indexed coherent tuples epsilon=1, giving the positive expression D*J-1.
The shifted fourth source port must first have beta subtracted; using that
port directly as MF_native would be wrong, and the review avoids that error.

## Controller scope and literal supporting data

The dummy obstruction is appropriately conditional. At fixed N,h and fixed
alpha=A(J), two accepted words differing by one independent safe dummy
toggle would have `deltaF=-deltaC`. Subtracting the two transport
congruences gives `(P+1)*deltaC=0 modM`. A signed power of two is a unit
modulo the odd M. At the stated canonical padded dimensions
`0<P+1<M`, so this is impossible. It follows that the old freely variable
pre-rank dummy family is not itself a family preserving the new fixed-gap
condition. It does not rule out coordinated changes or a new controller;
the review explicitly requires their separate unbounded completeness proof.

The complete native mask notes and compact44/indexed ordinary proofs were
read. Inert gzip decoding authenticated all four materialized ports of
each coherent tuple against their own complete bindings. The tuples have
identical beta, MC and MF_native, but distinct K values; no K identity or
spliced tuple is assumed. The actual mask population sum is590069,
MC=6 modulo8 and MF_native=4 modulo8, which verifies the local residues
and epsilon=1. Both complete K values are below B^2. These literal checks
support the uniform ordinary arguments; they do not replace their proofs.

The corrected active brief sections2b,2d and2e now distinguish the decisive
retained-budget obstruction from the weaker cyclic/coset restriction and
the open selective-gap/controller work. The final research obligations
retain whole coherent coefficients, transport, carry/anchor/alignment and
rank-controller completeness. No numerical nine-positive bound follows.

Only read-only standard-library hashing, inert coefficient decoding and
Git-blob comparison were used. No incoming program, native builder,
prototype checker, compiler, engine, Lean command or formalization was
run. The author review folder, frozen packets, active brief and canonical
PDF/TeX were not changed by this peer review.
