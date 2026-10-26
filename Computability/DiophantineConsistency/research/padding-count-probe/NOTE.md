# Padding tests before decoding: the C1005/L2011 lead

This isolated exploration retains the entire sorted942 tile language,
all3297 doubled coefficients, the marker at1004, all978 physical positions
and all978 native tests. It moves the sole clause from1462 to1005 and
uses L2011, with rho=2^47 and M'=2^45. Its four complete integer ports
occupy47,313 minimal unsigned bytes, compared with58,125 at the frozen
phase-split2471 checkpoint. Neither the accepted equation nor its files
are changed. This is not a minimum claim or a substitute for the new
complete native proof.

The exact source is the frozen `../phase-split-independent/certify.py`,
SHA256 `d7f42234adce10ee050168ebdced4a08b2d2c109910967c17b8b0038b61110ef`.
The probe authenticates it before import, and it in turn authenticates
the complete seed/page/decoder and ordinary source proof. No submitted
archive implementation is imported or executed.

## The new dependency argument

Let b be the fractional binary phase0..46 and n the number of selectors
in a current cell. Before any alignment, count or label decoding, the
complete cyclic carry bound is still0..57. The complete raw local
convolution, together with the temporal and spatial allowances, checks
that bound at the new clause position.

At clause1005 the non-temporal value is the complete doubled reflected
clause plus x_1. The shared bare18 input987 and spatial input996 are
absent. Every selector coefficient is2 modulo2048 and every label
coefficient is0 modulo2048. Thus the tested low part is

    2n+k+x_1+2^b*epsilon,       0<=k<=57, epsilon in{0,1}.

For b=0..6 it is at most1884+57+1+64=2006<2048. The nine clause tests
at bits2..10 force it into0..3 and hence n<=1. For b=11..46 the
temporal term vanishes modulo2048, and the remaining part is at most
1942<2048, giving the same conclusion. Neither case decodes labels.

The four phases7..10 need a different preliminary bound. The actual
existing padding tests bit3 at every field1..916. The complete suffix

    T459=sum_(e>=459)c'_e=137820284543942

satisfies T459+1024+60<rho. At every field h=0..546, reflected
coefficient indices are at least1005-h>=459. Thus its complete raw
value plus incoming carry is below rho even before any count recovery.
Every outgoing carry there is zero. This includes field63, the
predecessor of the first staircase test.

For each of the483 consecutive tested fields h=64..546, put

    S_h=x_0+...+x_(h-64).

The reflected selector coefficients have exactly these sources:
their indices are1005-h+f<=941 if and only if0<=f<=h-64.
Each contributes2 modulo2048. Every other reflected coefficient is a
label coefficient and contributes0 modulo2048. The bare marker is above
this band. The bare18 and spatial9 terms together contribute a number
u in0..2, and the temporal term is a multiple of16 for phases7..10.
With zero incoming carry, the actual padding digit therefore has residue

    2*S_h+u modulo16.

The prefix starts at zero just before field64 and increases by a Boolean
amount at each field. If it ever reached four, its first value four
would give a residue8,9 or10 and fail the actual bit3 test. Hence
S_546<=3. This controls exactly the first483 selectors, so

    n<=3+(942-483)=462.

The clause low part is now at most924+57+1+1024=2006<2048.
Its bits2..10 therefore force n<=1 in these four phases as well.
The probe checks every483-step residue transition for all four phases,
and every count/carry/bare/temporal quadruple in the47 stated regimes.
The finite state calculation overapproximates the two Boolean unit
sources by an independent u in0..2; this only enlarges possible states.

All phases now have n<=1, with no recovered labels or alignment used.
For any low field h<=1003, a control source f>=942 has reflected
coefficient index1005-h+f>=944. Its total is bounded by the sum of all
doubled label coefficients, M'-2048. Selector sources contribute at
most one coefficient, strictly below M'. Consequently

    E_h+3+rho/2+57 < 2M'-2048+rho/2+60 < rho.

Every outgoing carry through1003 is zero. The forced selector0 gives
an odd bare contribution at marker1004, all reflected contributions
are even, and its incoming carry is zero. The actual marker test forces
an odd temporal digit and excludes all nonzero b. Its own outgoing
carry is not needed for this argument. After b=0, the original whole
count lemma recovers every label. The same full935 whole-field phase
partition, including the two global Start-cycle exclusions, then aligns
the word. This is the complete order of the new preliminary steps.

## Adjacent marker and clause

The first reflected exponent is20. The bare18 coefficient remains one;
the bare marker at1004 instead has full coefficient
1+c'_1=30099357829123. All other reflected coefficients occur once.
Every coefficient remains below rho.

The predecessor of clause1005 is marker1004 itself. After alignment its
full raw value is

    Aadj+x_0+temporal_marker.

The actual copy parity imposes temporal_marker=x_0. More conservatively,
both summands are Boolean, so the established adjacency bound gives

    Aadj+2+57 <= 2M'-2048+59 < rho.

This resets the carry into the clause. The aligned clause has no temporal
or spatial source, and its occupied values are M'+2+x_1, which pass its
unchanged mask M'-4. The marker's bit0 test and the clause's bits2..44
are in distinct fields. Merely moving the clause to1004 with the same
canonical scheme fails: the Start clause would receive both x_0=1 and
temporal_marker=1, yielding M'+4 and violating bit2. This negative
control is scoped to that particular canonical scheme.

All seventeen copy identities retain their exact odd parts. Every
aligned padding reflection has a selector source at most896; one-hotness
therefore bounds its residue modulo2048 by0 or2, and the three Boolean
units give a residue0..5. All916 bit3 tests still pass for every safe
dummy subset. The complete product ends at2009, with value c'_0*x_1004;
field2010 is raw and actual zero. The ordinary dummy exponents are
1982,986,977, with the explicitly combined local collision at1981.
All required degree-plus-one margins exceed three fields.

## Full fixed controller and reproducible boundary

L2011 is prime and d=47*2011=94517. The exact base-two orders modulo
47 and2011 are23 and402=2*3*67, both coprime to d. Their lcm is9246.
The auxiliary prime is120199=13*9246+1>d. The complete whole-K residues
are:

| p | B | K | B squared | 1+BK+B squared |
| --- | --- | --- | --- | --- |
| 47 | 37 | 26 | 6 | 29 |
| 2011 | 1283 | 1995 | 1091 | 674 |
| 120199 | 37435 | 114787 | 99283 | 36379 |

The valuation-one lift is7300767062=1+120199*60739 modulo120199 squared.
The complete controller search, all four integer ports, every low/copy/
padding array, the full two512-state graphs, actual mask populations and
rank controls are in `RESULTS.json`. Constants are independently rebuilt
from their full recipes and compared with the authenticated whole-tuple
route. The script uses explicit failures, including under Python `-O`.

Run `python -B probe.py` or `python -B -O probe.py` to reproduce the
frozen receipt read-only. The complete ordinary proof and final bound
certificate will be separate deliverables in
`../padding-staircase-independent/`; this exploration neither promotes
a page nor claims that finite tests establish the unbounded theorem.
