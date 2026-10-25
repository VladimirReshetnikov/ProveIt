# Exact mathematical and execution scope of the modular probe

This is a proof of a bounded algorithm, not evidence that it has run. The
program and all future numerical unit results remain under execution
hold; only the mod5 check has an already proved expected value. Unknown unit
residues are not premises or asserted constants. Source paths/hashes and
closed inventories are in SOURCE_PINS.json.

## 1. One accepted tuple and one fixed formal polynomial

The preserved compact66 parent and indexed-tile parent specify the SAME
whole four-port tuple beta,K0,MC,MF. Their port dictionaries and all four
compressed byte strings must agree. The checked gzip/raw hashes and bit
lengths cover all295388 accepted raw bytes. Raw numerals use minimal
unsigned little-endian encoding: the last byte is nonzero and the length
is ceil(bit_length/8). This convention is explicit in the pinned indexed
builder and independent checker. The probe rechecks it by the last byte
for all ports, and converts only the existing K bytes with
`int.from_bytes(raw, 'little')`. It does not interpret the other three
whole integers, regenerate a tuple, import those parent programs or rerun
their native theorem. All parent members and the two accepted radix-note
reviews are bound as whole files before these operations.

Let the exact ordered accepted list be t_i=(w_i,n_i,e_i,s_i),0<=i<943.
The pinned whole TILES.json gives that list; it is not an arbitrarily
reordered tile set or a mixture with an older sorted selector order.
Every coordinate is an integer, with widths8,9,8,9 respectively. Define

    c_i = 1+2^10*(2^34-w_i-2^8*n_i-2^17*e_i-2^25*s_i).

This is the displayed complemented-payload form. The original indexed
constructor instead uses

    v_i=w_i+2^8*n_i+2^17*e_i+2^25*s_i+127*2^34,
    c_i=1+2^51-2^10*v_i.

The forms agree because2^41-127*2^34=2^34. All selector coefficients
are positive and below2^45; all control coefficients below are at most2^50.
Their ordinary values, rather than residues, are compared between routes.
The field widths make the packed coordinate value injective, so the full
coefficient comparison also binds every coordinate of each ordered tile.

The four literal printed control groups are

    2^10*x^1003*(x^20+2^17)*G8(2*x),
    2^18*x^983*(x^30+2^17)*G9(2*x),
    2^44*x^992*(x^39+2*x^30+4*x^19+8),
    2^48*x^1095*(1+2*x^1100+4*x^2201),
    Gm(x)=sum_(j=0)^(m-1) x^j.

Their independent literal expansion in the probe is:

    e=1023+j,c=2^(10+j), j=0..7;
    e=1003+j,c=2^(27+j), j=0..7;
    e=1013+j,c=2^(18+j), j=0..8;
    e=983+j,c=2^(35+j), j=0..8;
    (e,c)=(1031,2^44),(1022,2^45),(1011,2^46),(992,2^47),
          (1095,2^48),(2195,2^49),(3296,2^50).

There are41 such controls, disjoint from selectors0..942 and from each
other. Together they define Phi(x)=sum_(e=0)^3296 c_e*x^e. Its nonzero
support is exactly

    {0..942} union {983..992} union {1003..1011}
    union {1013..1031} union {1095,2195,3296},

with984 members. The native986-position support additionally contains
zero dummy holes1063/1064. Every remaining coefficient, including both
holes, is represented explicitly by the3297-entry array and compared.
The accepted Start0, Forbidden1 and initializer929 associations are also
checked, as is distinctness of all943 tuples. Full source hashes retain
the accepted machine/selector proof; this probe is not a new machine
decoder, TeX parser or source/native proof.

## 2. Independent recovery from the existing67-bit K

Put t=2^67 and

    base(t)=t^30+t^62+t^1100+t^2201+t^8849,
    P(x)=x^3296*Phi(1/x)=sum_(e=0)^3296 c_e*x^(3296-e).

The actual pinned formula gives

    K=base(t)+(t^4393+t^5495)*Phi(1/t),
    K-base(t)=t^1097*(1+t^1102)*P(t).

Here1097=4393-3296,1102=5495-4393, and8849=8807+42.
Thus Route B first subtracts exactly the five visible powers, requires
a positive remainder, and performs both exact divisions, with zero
remainders. It then extracts exactly3297 base-t digits and rejects any
remaining high part. Since0<=c_e<t, uniqueness of nonnegative base-t
digits proves that the reversed extracted list is exactly(c_0,...,c_3296).
The list is compared in full to Route A. This binds the order, not merely
the multiset, and every control/dummy/zero coefficient. Only the accepted
old integer K and its old reversed polynomial value are used here; no
new65-bit coefficient packet is formed or emitted. The old formal Phi
coefficients themselves are independent of the radix.

## 3. Two modular calculations of precisely the same new bracket

For each fixed prime p in{5,13,8807,581197}, put r=2^65 mod p and
b=r^8807 mod p. All four primes are odd, so r has an inverse. Route A
uses the complete tile-derived coefficients to sum Phi(r^-1) directly:

    kA = r^30+r^62+r^1100+r^2201+r^8849
         +(r^4393+r^5495)*Phi(r^-1) mod p,
    hA = 1+b*kA+b^2 mod p.

Route B uses the independently recovered coefficients and positive Horner
evaluation. Iterating pH<-r*pH+c_e for e=0..3296 computes exactly P(r),
because the exponents in P decrease from3296 to0. It then computes

    dcB = r^30+r^62+r^1100+r^2201
          +r^1097*(1+r^1102)*P(r) mod p,
    dr = r^42 mod p,
    kB = dcB+b*dr mod p,
    hB = 1+b*dcB+b^2*(dr+1) mod p.

The factorization of Section2 is a Laurent-polynomial identity at every
invertible r. Also r^8849=b*dr. Consequently kA=kB and hA=hB. Both
equal the complete coherent65-bit FORMULA's H0=1+B*K+B^2 modulo p;
neither route substitutes the old67-bit K residue. All65-bit powers
are evaluated by three-argument modular pow, or modular accumulation;
no unmodded65-bit B, beta,K,MC or MF is constructed. There is no search,
other bit width or modulus in the program. Parent primality/order/lift
contracts are retained; this probe does not reprove those contracts.

The accepted bounded note proves symbolically that hA=hB=4 modulo5,
which is required as a consistency check. No value or nonvanishing claim
is required for the other three primes. Since they are primes, a nonzero
H0 residue is a unit, and a zero is a genuine failure of that unit premise
for this literal template. The receipt distinguishes successful algorithm
verification (`status: PASS`) from the resulting Boolean
`candidate_units_nonzero`. The scientific Boolean may be false without
changing verification success, repairing inputs or selecting a new radix.

## 4. Controls and integrity boundary

The seven negative controls alter actual/private-copy inputs to the SAME
verification functions: one ordered tile coordinate, a tile-order swap,
a Boolean label, a nonzero dummy coefficient, one actual control
coefficient, the low bit of old K, and a redundant high zero byte on K.
Each must fail at its named semantic check, rather than merely an outer
file hash. The control-coefficient and dummy changes concern the literal
Phi expansion model; there is no claimed mutant file generated on disk.
Two valid controls reverse the order of the control contributions and
split one coefficient into two positive summands at the same exponent.
Integer addition preserves their complete Phi, so both must pass. They
show that semantic checks, rather than an assumed representation order,
are being exercised. Negative controls stop before modular evaluations;
valid controls compare full coefficients without evaluating residues
again. The original model is compared with its saved deep copy after
all controls. No parent input or caller object is mutated.

SOURCE_PINS flattens the three closed parents, selected additional proof
dependencies and the unchanged ordinary radix reviews. Authentication
checks all named bytes, exact parent member sets (including nested
manifests), own complete held membership and own code/prose pins before
arithmetic; the identical authentication is required after verification.
The self-hash inventory is anchored by the separately reviewed held seal;
it is not a signature or a claim that a wholly rewritten packet would
authenticate against that external trust anchor. Standard-library imports
only occur; no parent, producer, checker, native or page module is loaded.

The sole write is exclusive creation of a chosen fixed absent JSON path
under/tmp. Normal and optimized modes each have one first and one ROOT
fresh path. Symlinks and repository-contained output paths are rejected.
The stdout serialization is exactly the receipt bytes. The selected path,
run ordinal, durations and PIDs are absent from that serialization, so
same-mode fresh runs can compare every byte. Shell stdout/stderr capture
paths are documented separately and are not mathematical receipt fields.
No source/data directory, native word, new tuple, polynomial, coefficient
byte packet, TeX/PDF or Lean output is created.

## 5. What a successful run would and would not establish

After separate runtime release, a PASS would establish exact source
binding, full two-route Phi agreement, full modular route agreement and
the controls, while reporting the literal four residues. Nonzero values
at the three unknown primes would close those three finite obligations
of the accepted bounded note. A zero would instead record its exact
controller obstruction. Neither outcome supplies the still separate
replacement65-bit native interface, all carry/mask/alignment premises,
cofinal actual-rank construction or both fresh native/Pell witness maps.
No65-bit complete equation, numeric tuple, byte saving or page reduction
is accepted by this package. All existing67-bit files and formalization
boundaries remain unchanged.
