# Ordinary proof of the held finite computation

This document proves what the specified finite algorithm would certify.
It contains no observed application result. Its scope is the exact
accepted tile-biased49/L2033 instance, not a new native or Pell theorem.
All unbounded carry/alignment/occupation/subset/rank/Pell arguments are
the separately accepted complete parent proof. No incoming source code
is adopted. The executable closure consists of probe.py alone.

## 1. The hash-only coefficient input is a transparent table shortcut

The sole numeric input is the entire3297-element list
`../parity-clause-independent/coefficients.json`, SHA256
626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f.
This is the original unpermuted admissible942 table, not a later reversed
or sorted array. The accepted2999 proof section3 gives, for every j0..941,

    old_c[j]=1+1024*(1+u[j]),
    u[j]=w[j]+2^8*n[j]+2^17*p[j]+2^25*s[j],
    0<=w,p<256, 0<=n,s<512.

Its table is the complete table on the pinned2999 equation.tex. The
admissible index map is g(0)=0 and g(j)=j+1 for1<=j<=941; omitted old
index1 is the nonaccepting initializer. The whole printed942 table was
separately transcribed and compared with that bijection in the retained
BUILD_AUDIT and ordinary/page reports. The finite certificate explicitly
binds recipe_bindings.all3297_coefficients_sha256 to the hash above,
alongside the actions, tiles and seed hashes. SOURCE_MANIFEST binds that
certificate, proof and entire printed page. These exact files and the
ROOT acceptance are pinned as inert mathematical/provenance premises.
No value for this new instance is obtained from old2999 compressed ports.

The mixed-bit bounds make u's four components uniquely recoverable.
Thus (old_c[j]-1)/1024-1 recovers EXACTLY the printed word u[j]. Since
the bit widths total34, 2^34-1-u[j] is its componentwise complement:

    wbar=255-w, nbar=511-n, pbar=255-p, sbar=511-s.

This is an exact identity, not a guessed program index. The probe hashes
the entire raw old JSON before parsing. It checks list length3297 and
genuine int entries, every selector's congruence and unsigned34-bit bound,
all34 old label powers, and every other coefficient zero. No suffix or
zero tail is dropped. Hash authentication plus this retained table proof
licenses the numeric shortcut without executing the table decoder.

## 2. Two complete new encodings

For j0..941 and h in960..968 or987..994, define

    eps_h(j)=floor((h+877-j)/942).

Here896<=h+877-j<=1871 since h>=960 and j<=941. Hence eps is0 or1. More directly,
the denominator and index ranges give the exact equivalence

    eps_h(j)=1 iff 0<=1006+j-h<=941.

The first route keeps the complemented low17 bits (wbar,nbar), and XORs
each THIRD packed bit17+i with eps_(987+i)(j), i0..7, and each south
bit25+i with eps_(960+i)(j), i0..8. It writes XOR as x+e-2xe and adds
the resulting bit weights. The second route constructs a toggle mask
using the direct interval condition and applies integer bitwise XOR to
the complete complemented34-bit word. The two routes must agree for
every selector. This checks the actual corrected p lane, not an
orientation nickname that might confuse it with the first w component.

Call the common word uenc. The accepted logical table has positive
complemented north and west colors, which are unchanged; hence uenc>0.
It is an unsigned34-bit word and therefore

    c[j]=1+4096*(2^34-uenc[j]) satisfies 0<c[j]<2^46=M.

The producer scales each authenticated old label by4. Independently the
consumer places explicit powers at ALL four lanes:

    c[978+i]=2^(12+i), c[969+i]=2^(29+i), i0..7;
    c[960+i]=2^(20+i), c[942+i]=2^(37+i), i0..8.

Both routes define zero at every remaining index through3296, including
dummy977 and marker1005. Full-list equality is required. The physical
support is separately Es={0..950} union{960..985} union{1005},978 sites.
In particular physical dummy/marker membership is not inferred from c.

## 3. Whole ports, independent kernels and masks

Fix rho=2^49, d=99617=49*2033, B=rho^2033 and beta=B-1. The producer
uses Horner on c[0],...,c[1006], including every zero. Its induction
invariant after position e is sum_(f=0)^e c[f]*rho^(e-f), giving

    DC=rho^18+sum_(e=0)^1006 c[e]*rho^(1006-e),
    K=DC+B*rho^9.

All nonzero e are<=985, so no negative exponent occurs. The consumer
uses the independently encoded full3297 list, termwise integer shifts
49*(1006-e), plus explicit powers18 and2033+9. The whole integers must
agree. There is NO bare marker rho^1005. At any tested modulus p a
third comparison reduces the actual whole K, versus a modular Horner
route and an independently encoded termwise modular-power route. Both
modular routes include both bare18 and spatial B*rho^9.

Let core=sum_(e=960)^968 rho^e+sum_(e=987)^994 rho^e+rho^1005. Define

    MC=beta-sum_(e in Es)rho^e,
    native=4+(M-2)*rho^1006+core
      +(rho-1)*sum_(e=2012)^2029 rho^e+(2^32-1)*rho^2030,
    MF_source=native+beta.

The separate checks use G_m=(rho^m-1)/(rho-1),

    MC=beta-G_951-rho^960*G_26-rho^1005,
    MF_source=B+3+(M-2)*rho^1006+core+2^32*rho^2030-rho^2012.

The last identity is the exact padding telescope, not a numerical
approximation. All exponents, LOW32, source shift and origin4 are fixed.
The popcounts are pc(MC)=d-978 and pc(native)=978:64 core bits plus
18*49+32=914 padding bits. The probe checks these actual whole integers,
MC=2mod4,native=4mod8,0<MC<beta,0<native<beta and0<DC<B. The four ports
are saved ENTIRELY as minimal positive unsigned big-endian bytes. Their
hash/length records refer to those whole bytes, without decimal limits,
gzip, external tables or hidden precision truncation.

## 4. Complete finite controller and explicit scientific rejection

The independently accepted small arithmetic proves d=7²*19*107,
ord_d(B)=954 and that B²-1 is a unit at all fixed prime divisors. The
probe also checks the full order facts directly: base2 orders21,18,106
at49,19,107; B orders3,18,106 there; and order954 at WHOLE d. Each check
uses a full exponent giving1 and every prime-divisor proper exponent
not giving1. For954 the proper divisors are954/2,954/3,954/53. This
standard group argument proves exact order; checking only modulo7
would omit the required square49. The supplied factor sets are complete
by the accepted hand factorizations, not discovered by the probe.

For p=7,19,107 it records B,K,H=(1+BK+B²) modp using the three K routes.
If any H=0, the whole-d unit premise is false for this fixed tuple and
changing lambda cannot repair it. The status REJECTED_FIXED_PREMISE is
therefore an honest rejection of this controller hypothesis. All three
residues and all port/coefficient bytes are retained. No prime search is
attempted; no equation/native impossibility or old endpoint is claimed.

Otherwise the algorithm tests exactly lambda=954*k+1, k105..304. This
is200 candidates and the first exceeds d since954*105+1=100171>99617.
An odd trial-divisor loop returns the least factor or0. An independent
validation tests EVERY integer divisor in the pertinent interval. For
factor0 no divisor2..floor(sqrt(lambda)) exists, proving primality. For
a nonzero factor it verifies divisibility, the square-root bound, and
the absence of every smaller divisor. Thus candidate outcomes do not
depend on a probabilistic test or a shared primality implementation.

For each prime it requires lambda>d, lambda=1mod954 and Fermat's
B^(lambda-1)=1modlambda; records the complete residues; and tests
B²!=1modlambda,H!=0modlambda. The lift residue is

    t=2^[d*(lambda-1)] modlambda²,
    lift_quotient=(t-1)/lambda.

Since t=1modlambda and0<=t<lambda², the quotient lies0..lambda-1.
It is nonzero exactly when the valuation is ONE, rather than>=2.
Success plus the fixed tests is exactly P_bias as reduced by the
accepted2033 proof: whole-d congruence, all units and valuation one.
It records every tested candidate and stops at the first success. No
successful prime or residue is asserted in this held document.

An exhausted interval gives REJECTED_BOUNDED_SEARCH and retains the
whole200-candidate trace. It does not refute existence outside the
interval. Both rejection outcomes are normal scientific results, with
zero process exit; an exception indicates an actual execution failure.

## 5. Controls, optimization and complete byte reproduction

Main invokes validate_model on the actual producer outputs BEFORE any
controller search or output serialization. That production gate compares
the complete producer coefficients with the independent XOR route,
the physical set with the independent disjoint-lane union, and every
whole port with the independently computed termwise/closed-form ports.
Every coefficient, physical or port mutant below passes through THIS
SAME production gate, not a separate test-only mirror. Both valid and
negative paths use genuine types and complete values.

All checks use explicit need/ValueError, never assert. Each negative
control requires the intended exact exception reason and rejects an
unexpected exception or acceptance. Actual complete-array mutations
change selector0, label969, and zero-tail3296. Physical deletions remove
dummy977 or marker1005 from Es and recompute MC by adding rho^e; their
actual whole mask gains the forbidden bit and one popcount, before the
complete physical-model guard rejects them. Port mutations change K,
beta, delete MF_source's beta shift, or restore the obsolete bare marker.
Other controls reject9 as prime, order318 instead954, duplicate JSON,
nonfinite JSON, and genuine Boolean/float entries in a coefficient list.
The total is15 negative cases. Five positive cases exercise the whole
copied/reordered model, primes7/19/107 and least-factor(9)=3. No fabricated
output list substitutes for performing these checks.

The default path recomputes both encodings, all whole ports and modular
routes, full bounded controller trace and controls, then compares all
six output members and every saved byte. This includes the entire
coefficients and raw ports, not just saved hashes. A write run creates
an absent data directory and exclusive files; a partial failed run is
preserved, never cleaned or retried under this authority. The before
and after authentication bind self code, input bytes and accepted proof
scope; strict JSON rejects duplicate/nonfinite values and exact integer
checks reject bool/float. Relative pin paths reject traversal/symlinks.
All stdout is a deterministic canonical JSON report with exact scientific
status. Normal/O and same-mode fresh whole captures must match bytewise;
this is a requirement for future observed evidence, not an existing fact.

## 6. Limits of any later success

The ordinary parent proof, with its two nonauthor reviews and ROOT's
separate conditional acceptance, supplies all count-before-phase,
local-only E_h bound, logical decoding/occupation, all padding/subsets,
actual-rank/full-modulus transport and both complete15-positive P66 maps.
A successful finite record discharges ONLY its P_bias(49,2033). It does
not change the proof to Carrier65, prove minimality, decide consistency,
assert actual unsolvability, replay an internal ZFC/Lean kernel or
authorize a new printed page. A failed finite condition likewise gives
no counterexample to the conditional mathematics or existing endpoint.
