# Independent review of the one-anchor L=7309 construction

**Result: pass for the new complete ordinary native argument and its finite
certificate, relative to the retained ordinary arithmetic, machine and
syntactic-refutation contracts.** No unresolved gap was found in the new
weighted clause, selector-count copy, phase recovery, carry, padding,
canonical-subset or controller arguments. This does not claim a fresh
end-to-end proof-assistant or internal-ZFC formalization of those inherited
contracts.

The reviewer read all 556 lines of the final ordinary proof, its README,
the entire new finite verifier, and the finite receipt's principal data.
The entire receipt and coefficient array were then independently reproduced
and compared byte for byte by both normal and optimized Python execution.
The mathematical author was `/root/complemented47_review`; the finite-code
author was `/root/circuit_reduction`. This reviewer authored the earlier
hash-pinned decoder used by the new verifier. Thus the new construction and
implementation received separate review, but the decoder was not implemented
twice independently.

## Fixed model and weighted clause

The complete old table, 436-character seed and decoder remain pinned. The
coefficient array removes the three M-valued flags and inserts one 3M-valued
flag at 2079, preserving the total coefficient sum. There are 978 positive
coefficients and 980 physical support positions, including both dummies.
The actual maximum coefficient is **3M**, and this is used in the new
extra-dummy bound. The shared Psi polynomial gives the weighted controls at
t=2 and their exact support indicator at t=1; its factor 2t-1 is necessary.

For every incoming carry 0..29, n+k<1024 makes the nine low count tests
force n<=1. In the occupied case the remaining payload is a positive
multiple of 2^36 below 5*2^34. Reduction modulo 2^34 recovers the copied
label value and leaves 1+3a=4, hence the flag is one. The empty case has
W=a=0. The occupied raw clause is 2^46+1<rho. These statements do not
assume preexisting copies, occupation or aligned temporal transport.

The two 45-bit clauses, 17 label copies, count copy and origin test have
109 bits. The 871 padding bits yield native population 980, complementary
to MC. The finite verifier checks the actual large integers, their scalar
boxes and origin residues, and the once-shifted source mask. Its positive
padding sum equals the telescoping printed expression exactly.

## Arbitrary phases, clean clauses and alignment

Difference 1067 is absent from the whole physical support, including both
dummies. Thus each reflected coefficient has at most one Boolean
predecessor at a fixed output, giving the entire coefficient-sum bound.
The 943-term unit block plus bare/spatial terms contribute at most 946.
For the extra 0/2 dummy, unit outputs 2200..3142 precede every reflected
dummy output, whose minimum is 3145. The remaining three dummy outputs
are separate lower fields. The total extra allowance 6M is therefore valid.

Adding every fractional temporal phase and carry 29 gives a value below
30*rho. The monotone cyclic carry map preserves 0..29 and stabilizes from
zero. Soundness identifies the resulting residue word only after the
outer argument supplies strict F; completeness constructs it first and
proves strict F from the new tail. There is no circular no-carry premise.

The temporal support is a translate of the physical support even in phase
46: its possible odd spill moves dummy1063 into the already supported
1064. Since 1067 is absent, one clause is clean in each cell and gives the
entire tile/label/flag decoding before phase alignment.

Every field through 2081 has zero outgoing carry because reflection starts
at 2082 and the conservative total is bounded by
952+3*rho/4+29<rho. In the forced Start cell the copied south bit at 1014
is one, and the new count-copy field 2079 is also one. Both receive zero
incoming carry and demand odd temporal contributions. Phases 1..45 give
only even digits; phase 46 has an odd spill at only one residue per cell.
Hence the phase is zero. The unique support difference 1065 is
2079-1014, so the remaining whole-field offset is zero as well.

## Every copy, predecessor, padding field and origin

The finite checks cover all nine temporal and eight spatial copy fields,
the complete selector-count convolution, both full clauses and their
predecessors. After alignment, the count test equates the Boolean selector
count and temporal flag; it does not assume a second physical flag.

The upper clause predecessor is **Aadj+2^18*x2079**, not Aadj alone.
Difference 1066 has exactly the representation 2079-1013, whereas 1068
is absent. The complete unit product ends at 4158, before either clause
predecessor. At most one selector and the label sum contribute to Aadj,
so Aadj<=2M-1024; the extra term and carry 29 still fit below rho. Both
clause carries therefore reset before the exact occupied/empty clause.

The padding predecessor 6324 is exactly 2^35*x2079 and resets. Every
field 6325..6364 is formally zero, covering all 18 full padding fields and
the low 25 bits at 6343. The last potentially nonzero field 7307 is
c0*x2079 with c0<M; its outgoing carry is zero. Field 7308 is genuinely
zero. This resets all cell origins and gives the stronger fresh bound
F<q/rho. No old packed word or tail estimate is reused.

Spatial equality propagates occupation through the one-cell rotation from
forced Start, because complemented genuine colors are positive and empty
colors are zero. Start's unequal north and south colors exclude zero
temporal stride. The inverse color bijection then has exactly the retained
marked computation/refutation interpretation.

## Actual rank and complete controller

Every simultaneous safe low-dummy subset preserves the same resets and
gives 0<F<q/rho, C<q/rho^5229 and 2C+F<q/3. The binary rank decomposition
uses the actual defining R and the source mask shifted once; disjointness
gives pc(R)=3t+2, while the origin residues separately give R=3 mod4.

The safe increment has local degree at most 6291 and spatial/temporal
degrees 1105 and 1063 in later interior cells. Distinct kernel residues
and coefficients below rho bound all three contributions. The corrected
finite guard uses exponent-plus-one margins 6292,1106,1064, so their sum
is below q/rho^2. Uniform subset slack lifts the modular increment to
the ordinary equality deltaF=deltaRaw. Substitution in the defining rank
then gives deltaR=-Gamma*B^j without treating rank as an independent knob.

The exact prime-field order at 7309 is **1044**, not 7308. Both base-2
and B orders are checked with every prime factor 2,3,29; their gcds with
d are one. The new kernel has nonzero H at all three relevant primes.
Together with B^2!=1 and the valuation-one lift, this makes Gamma a unit
at every prime divisor of dN. LTE and CRT produce the full stated orbit.
The consecutive-coordinate subset argument uses an a0 coprime to its
pure lambda-power length; the optional B^3 term ensures such an a0.
All selected positions and their spatial/width translates stay interior.
Thus the prescribed residue is attained by the actual rank, yielding
positive w and z satisfying transport.

The retained whole P66 witness maps use the same scalar hypotheses and
positive bridges. Odd d,N,R preserve the square conditions. Completeness
has actual Ns=Delta and the other five factors one. The unchanged symbolic
front therefore remains fifteen positive variables, 66 integer-leaf
operations and exact degree 157. This does not assert equality between
different old and new specialized polynomials.

## Reproduction and exact receipt

Both read-only commands passed after the final margin correction:

```text
python3 research/one-anchor-independent/certify.py
python3 -O research/one-anchor-independent/certify.py
```

All checks use explicit exceptions, so optimization retains them. Default
execution compares certificate and coefficient bytes and does not write.
Only explicit --write materializes them. The source proof, decoder and
complete seed page are hash-pinned before use. The decoder code's pinned
path refers to that exact page. Trial division establishes the relevant
primes, and complete factor reduction establishes exact orders. Dense
reciprocal Horner evaluation, direct tile/control expansion and the whole
integer agree on K at every controller modulus.

An exploratory convolution check initially allowed only one spatial unit;
review requested three to cover the extra dummy, and the final verifier
uses three. ROOT also requested the exponent-plus-one increment margins
noted above. Neither correction changes any constant or final result.

| Quantity | Reproduced result |
|---|---|
| L, d | 7309, 343523 |
| Orders at 47 and 7309 | 23, 1044 |
| Controller spacing | 24012 |
| Auxiliary prime | 360181=15*24012+1>d |
| H at 47,7309,lambda | 40,597,144105 |
| B^2 modulo lambda | 176616 |
| Lift modulo lambda squared | 14875835482=1+41301*lambda |
| beta,K,MC,MF source bytes | 42941,43188,42941,42941 |
| Complete raw tuple | 172011 bytes; 8976 below the two-anchor7691 tuple |

Exact reviewed SHA256 bindings:

```text
PROOF.md       62f9aba2726737f1e9a507f5d28468f402a1702d9b59e2179138382ffc75dd6b
certify.py     9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d
certificate    f1d772729d85b1138205d8ab37297dcf79bfffd1338525fb59c22495adf325fd
coefficients   25ddb8782c5246e195c1f9d9f74909572b58d787da275bd86d88b21bd873601c
decoder        318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed
seed page      440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff
```

This review discharges the new finite Pc1 through the executable receipt
and accepts the new ordinary argument within its explicit inheritance
boundary. It does not review a future printed page or authorize an
unexamined re-specialization of the layout.
