# Independent review of the zero-weight physical flag at L=6007

**Result: pass for the complete new ordinary native proof and finite Pc0
certificate, relative to the retained ordinary arithmetic, machine and
syntactic-refutation contracts.** No unresolved gap was found. The physical
flag's delayed recovery is valid, and the implementation preserves that
flag even though its coefficient is zero. This review does not claim a new
end-to-end proof-assistant or encoded internal-ZFC replay.

The reviewer read all552 lines of the complete PROOF.md, the README, the
entire new certify.py and the receipt's principal data. The full certificate
and all3297 coefficient entries were reproduced byte for byte by normal and
optimized Python execution. The proof author was
`/root/complemented47_review`; the finite-code author was
`/root/circuit_reduction`. This reviewer wrote the earlier shared decoder,
so the new proof and implementation were separately reviewed, but the
inherited decoder is not claimed to have two independent implementations.

## The flag is physical before it is recovered

The physical support has980 positions, while only977 coefficients are
nonzero. Both dummies990,991 and the flag1984 have coefficient zero.
MC explicitly permits the flag's Boolean bit. Psi at one includes that
position; Psi at two removes its clause weight through the factor2-t.
Inferring physical support from the positive coefficients would change the
problem and invalidate the completeness argument.

The reduced mask mu=2^44-2 tests bits1..43. For every incoming carry0..29,
the low count bits force n<=1, and n=1 forces incoming carry zero. The
remaining34 tests give Q=0 modulo2^34. An empty cell has W=0; an occupied
cell has Q=2^34 and the correct copied labels. Its raw clause is M+1.
There is no flag term in this calculation, and no early conclusion that
the flag is one is used elsewhere in the proof.

The dependency order is sound:

1. A clean clause decodes only the selector count and labels.
2. In the forced Start cell, copied south bit1 at974 and the selector
   count at1984 are both one, independently of any flag value.
3. Their two parity tests exclude fractional phases and then fix the
   whole-field offset using the full physical support.
4. After alignment the count test gives exactly
   `a_(temporal predecessor of i)=n_i`.
5. Spatial label equality and the forced Start make every cell occupied.
   The temporal rotation is a permutation, so the displayed relation then
   makes every physical flag one.

This uses neither prior occupation nor unique Start nor a preferred
soundness stride. Start's unequal north/south labels subsequently exclude
zero stride as required by the retained computation interpretation.

## Every nonuniform copy and the unit-block separation

The nine temporal tests973..981 receive the south fields943..951 through
shift30; their shift20 and spatial10 predecessors are absent. The eight
spatial tests1012..1019 receive west992..999 through shift20 and east
1002..1009 through the next-cell shift10; their shift30 predecessors and
aligned temporal sources are absent. Dummy990 has shifted outputs1010,
1020 and1000, outside these tested fields.

The selector-count block1042..1984 hits exactly selectors0..942 at1984.
Reflection begins at1986. The block's nonflag products end at2993, and
its flag products occupy3026..3968. Consequently both clauses2995/4007
and both predecessors2994/4006 avoid the unit block. This separation
really needs two support intervals; simply bounding the maximum product
degree would not justify the lower clause.

Physical difference1012 is absent,1013 is absent, and1011 has precisely
the pair1984-973. The only physical difference1010 is1984-974. These
claims include the zero-weight flag and both dummies; the finite verifier
checks full support-pair sets.

## Global carry, alignment and every local reset

Removing3M from the previous coefficient sum gives
`Csum<28*rho+965470`. At a fixed output each reflected coefficient has at
most one Boolean predecessor. The unit, bare and spatial terms add at most
946. The extra0/2 dummy's unit outputs end at2974, before reflected dummy
outputs start at2976; its other three outputs are separate lower fields.
The complete extra allowance is less than2M, because every coefficient
is below M. Adding any fractional temporal phase and incoming29 remains
below30*rho. The monotone cyclic carry map therefore has a fixed point in
0..29 before any alignment assumption.

The possible phase46 odd spill is990 to991, already in physical support.
Absent physical difference1012 ensures a clean clause in every cell.
The resulting tile/label decoding does not constrain flags. Every field
through1985 has zero outgoing carry from the bound
952+3*rho/4+29<rho. Thus both Start phase tests receive zero incoming carry.
Phases1..45 give only even temporal digits; phase46 can supply an odd spill
at only one residue. At phase zero, the unique difference1010 fixes the
remaining field offset. These steps remain valid with arbitrary Boolean
flags in all other cells.

The lower clause predecessor is Aadj. The upper is exactly
`Aadj+2^18*x1984`. The proof retains the extra upper term. In this layout
Aadj includes selector-to-label adjacency942->943 and dummy-to-label
adjacency991->992. The one-selector bound plus the entire label sum still
gives Aadj<=2M-1024. The extra0/2 part at990 does not alter Aadj, since
c991=0. Adding the flag term and carry29 stays below rho, so both clauses
receive zero carry regardless of the flag's value.

Padding predecessor5018 is exactly2^18*x1984 and resets. The only possible
high-band input in5019..5039 is1984, requiring absent coefficient indices
972..952. Thus the entire21-field band is zero, covering18 full fields
and29 low bits at5037. The final nonzero candidate5991 is c0*x1984 with
c0<M, so it resets; all15 later fields through6006 are zero. Cell origins
therefore reset as well. The shifted origin masks and safe dummy changes
have the same required literal interpretation.

The scalar/population recipe is coherent: two43-bit clauses plus19 other
tests give core105, and875 padding bits yield native980. MC clears979
ordinary physical bits plus the extra dummy bit. The source mask shifts
the native mask by exactly one beta. The verifier checks these statements
on the full integers, including the positive-sum/telescoping padding
identity and the scalar boxes needed before native interpretation.

## Fresh subsets, actual rank, controller and complete P66

Completeness encodes new complemented words on this exact support, with
the physical flag set to one canonically. It does not obtain those flags
from a weighted clause. Every simultaneous safe low990 subset preserves
the masks, copies, clauses, padding, flags and origins. The final zero
field gives F<q/rho, and physical maximum1984 gives C<q/rho^4022.
These bounds imply2C+F<q/3 and strict F before using the outer converse.

The binary rank decomposition uses the actual rank and the once-shifted
source mask. It yields pc(R)=3t+2, with R=3 modulo4 independently obtained
from the origin residues. For an interior safe bit, the local/spatial/
temporal increment exponents are4997,1000,990. Distinct residues and the
exponent-plus-one margins bound their sum below q/rho^2. Uniform subset
slack lifts the congruence to the ordinary equality deltaF=deltaRaw;
therefore deltaR=-Gamma*B^j is an identity of actual ranks.

The new finite data verify the exact orders23 and1001=7*11*13 at47 and6007,
including every proper-order test and the gcd conditions. H is nonzero at
both fixed primes and the new auxiliary prime; B^2-1 is also nonzero there.
The valuation-one lift supplies the full lambda-power orbit by LTE, while
CRT supplies its stated form modulo dN. The consecutive-coordinate subset
argument and its optional B^3 term remain valid. The bounds keep all
selected cells and both translates inside the word. Hence the required
residue is attained by the actual rank, giving positive transport witnesses.

Both full P66 directions retain the same coefficient-independent arithmetic
contracts and positive multiplication bridges. Odd d,N,R preserve the
square conditions. Completeness makes actual Ns=Delta and the other five
factors one. The front remains fifteen positive variables,66 integer-leaf
operations and exact degree157; no equality with another specialized
four-port polynomial is asserted.

## Executed checks and missing-flag negative control

After full source inspection, both read-only commands passed:

```text
python3 research/zero-weight-flag-independent/certify.py
python3 -O research/zero-weight-flag-independent/certify.py
```

All gates use explicit exceptions, so optimization retains them. Default
execution compares the complete certificate and coefficient bytes; only
explicit --write materializes them. The parent verifier, decoder, seed page
and both mathematical proof bindings are checked transitively before use.
Long receipt arrays are summarized only after full elementwise comparisons,
not compared by a hash in place of the mathematical check. Trial division
and complete order reduction provide the elementary finite evidence.
Reciprocal Horner evaluation, direct tile/control expansion and the whole
integer agree on every modular K evaluation.

A separate newly authored, read-only negative control loaded the exact
reviewed verifier, formed `missing_flag=support-{1984}`, and passed that
set to geometry and whole_constants without modifying any source. Geometry
rejected the phase pair, physical flag, upper predecessor, padding and
tail identities. Whole constants raised exactly
`ValueError('Whole complementary populations')`. Thus the zero coefficient
cannot silently cause the physical flag to disappear from the checked MC.
For a later printed-page audit, deleting Psi's last `(2-t)` term is the
corresponding important source-corruption test: K is unchanged at t=2,
while the essential MC bit changes at t=1. This review does not claim to
have audited that future TeX page or its separate corruption suite.

| Quantity | Reproduced value |
|---|---|
| L,d | 6007,282329 |
| Physical / nonzero coefficient positions | 980 / 977 |
| Coefficient sum / maximum | 3829914518407087 / 15049678914561 |
| Core / padding / native population | 105 / 875 / 980 |
| Controller orders / spacing | 23,1001 / 23023 |
| Auxiliary prime | 368369=16*23023+1>d |
| H at47,6007,lambda | 2,53,95646 |
| B squared modulo lambda | 46186 |
| Lift modulo lambda squared | 135511167293=1+367868*lambda |
| beta,K,MC,MF source bytes | 35292,35350,35292,35292 |
| Full raw tuple | **141226 bytes** |

The raw tuple saves30785 bytes from the preserved7309 tuple's172011.
Printed recipe size, typography and page count are separate measures.

Exact reviewed SHA256 bindings:

```text
PROOF.md       ccfbcea8c2dd5502e896777f20234bddd23e16cf43cb67d267131258d3d753d7
certify.py     35669d519f1fdd283e7b498d36cc799f10a3bdc7b4924f40ce011724fe3942c5
certificate    6b25d6e2581822894fdc429bf4639ff009fa134599b8e569ee4b94de046afe5a
coefficients   eed70657080c55394ae5caf87305ee0323584a504b287b17f29d45bac04291eb
parent         9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d
decoder        318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed
seed page      440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff
```

This review accepts the new ordinary argument and discharges its finite
Pc0 through the reproduced receipt within the explicit inherited theorem
boundary. No earlier source, maintained equation, certificate or proof was
edited, and no commit was made by this reviewer.
