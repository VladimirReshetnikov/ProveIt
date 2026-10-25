# Exact bounded certificate algorithm and scientific boundary

This is an ordinary proof of the prepared algorithm, not an execution
receipt, prime certificate or calculated53-bit unit value. Every accepted
input and retained contract is wholly pinned before runtime arithmetic.
All unit values and candidate outcomes remain unknown in preparation.

## 1. Complete actual Phi and old four-port provenance

Use the EXACT accepted ordered list t_i=(w_i,n_i,p_i,s_i),0<=i<943,
with widths8/9/8/9. The selector formula is universally

    c_i=1+2^10*(2^34-w_i-2^8*n_i-2^17*p_i-2^25*s_i).

It equals the old complemented-payload formula1+2^51-2^10*v_i, where
v_i=127*2^34+w_i+2^8*n_i+2^17*p_i+2^25*s_i. The four literal control
groups expand to exactly

    (1023+j,2^(10+j)),(1003+j,2^(27+j)), j=0..7;
    (1013+j,2^(18+j)),(983+j,2^(35+j)), j=0..8;
    (1031,2^44),(1022,2^45),(1011,2^46),(992,2^47),
    (1095,2^48),(2195,2^49),(3296,2^50).

There are41 contributions, disjoint from the943 selectors. Every omitted
c_e is0, including1063/1064. The explicit3297-entry array has984 nonzeros,
with986 support positions when the two dummy holes are included. Field
packing is injective at these widths; the full coefficient equality binds
all ordered coordinates, not merely their multiset or a sampled hash.

Independently put t=2^67 and P(x)=x^3296*Phi(1/x). The WHOLE existing
indexed K satisfies the accepted exact formula

    base=t^30+t^62+t^1100+t^2201+t^8849,
    K-base=t^1097*(1+t^1102)*P(t).

The second route requires positive remainder and zero remainders in both
integer divisions, extracts exactly3297 base-t digits, requires no high
part and reverses them. Since0<=c_e<t, uniqueness of base-t representation
proves equality with every formal Phi coefficient. The old K is parsed
with its explicit minimal unsigned LITTLE-ENDIAN convention,592884 bits
and74111 bytes. All four old gzip/raw payloads and bindings are compared
across compact/indexed sources, covering295388 old raw bytes. The other
three old integers are not parsed as full values. No new53 integer is
constructed by this recovery, and no parent program is imported.

## 2. Two full modular formulas

For an actually tested odd prime p, set r=2^53 modp and b=r^8807 modp.
The direct route uses all tile-derived c_e to accumulate Phi(r^-1), then

    kA=r^30+r^62+r^1100+r^2201+r^8849
       +(r^4393+r^5495)*Phi(r^-1), hA=1+b*kA+b^2 modp.

The independent positive route uses EVERY old-K-recovered coefficient
in Horner order0..3296, computing P(r). It forms

    dcB=r^30+r^62+r^1100+r^2201+r^1097*(1+r^1102)*P(r),
    dr=r^42, kB=dcB+b*dr, hB=1+b*dcB+b^2*(dr+1) modp.

The factor identity and r^8849=b*r^42 prove kA=kB and hA=hB. These are
the complete coherent53 formula's K0 and Hctrl residues, not the residue
of old67 K. The positive route uses a manual binary modular-power routine;
its invariant is result*a^exponent equal to the original required power
modulo p. Halving an even exponent and removing its low bit establish
the invariant at each iteration. It terminates at exponent0. No unmodded
new B or K is used: all new products/powers reduce modulo p or lambda^2.

The cached positive certificates are computed from the second COMPLETE
array at precisely the same primes as the direct route. Actual-certificate
controls compare against those independent values through the same
typed-equality validator; they do not substitute an author-predicted
residue or a stale outer checksum. Every tested prime's positive route
is serialized as a complete companion certificate.

## 3. Prime certificates and independent validation

Only fixed53/8807 and lambda_m=228956*m+1 for3<=m<=66 are considered.
Candidates are odd and exceed d=53*8807=466771. The smallest is686869;
the largest is15111097. This is a finite64-candidate scope, not a theorem
that one is admissible. Old lambda581197 is outside this parameterization
and its incompatible spacing is not reused.

The generator tests divisor2 and then odd divisors through isqrt(n),
returning either the least divisor or a prime assertion with that bound.
The verifier independently scans EVERY integer2..isqrt(n), validates the
literal integer bound and compares the least divisor and Boolean status.
For n>1, if n were composite, its smaller positive factor would lie in
that interval; absence of every such factor therefore proves primality.
A returned divisor proves compositeness. All scoped n are odd and>1.
This is complete trial division, not a probabilistic primality test.

## 4. Exact orders, square units and first lifts

For a CERTIFIED prime p, B=2^d is a nonzero residue. Fermat gives order
dividing p-1. Generation factors p-1 by successive integer division,
then removes a prime factor q from its tentative order whenever
B^(order/q)=1. This terminates at the exact order.

Independent verification does not repeat that reduction algorithm. It
checks order|(p-1), a COMPLETE prime factorization of the claimed order
(each factor prime, distinct, positive exponent, product exactly order),
B^order=1, and B^(order/q)!=1 for EVERY prime q dividing order. All powers
use the separate binary implementation and independently reconstructed
B modp. Any smaller proper order dividing order would divide order/q
for some such q, a contradiction. Thus the order is exact. Permuting
factor/witness records is harmless; missing, repeated or changed records
are rejected. B^2 and its Boolean nonunit/unit status are also compared
exactly. A false square-unit status is a legitimate candidate obstruction,
not a malformed mathematical certificate.

At53 and8807 the exact orders MUST be52 and4403, respectively, as required
by the accepted ordinary proof. At a candidate lambda, its exact order
must exceed2; this is equivalent here to B^2!=1. The parameterization
makes228956=lcm(52,4403) divide kappa=lambda-1. All three square-unit
and spacing obligations are therefore explicit certificates.

Generation computes B^kappa modulo lambda^2 with two modular pow calls.
The independent verifier directly computes2^(d*(lambda-1)) modulo lambda^2
using binary powering. Fermat assures the result is1 modulo lambda;
the validator requires that fact. The integer B^kappa-1 has valuation
EXACTLY1 iff its lambda^2 residue differs from1. Thus `valuation_one`
is completely certified without constructing that enormous integer.
A false valuation flag must still be a correctly verified false condition.

## 5. Deterministic bounded science, separate from verification

First both complete Hctrl routes and fixed prime/order certificates are
verified at53 and8807. If either Hctrl is0, the explicit fixed-unit premise
of the accepted ordinary adapter fails. The scientific outcome is
`fixed-unit-obstruction`; the candidate list MUST be empty and selection
None. Verification itself may PASS with this obstruction. There is no
prime search to pretend that an unrelated lambda repairs a fixed zero.

Otherwise the program tests m in exactly3..66 in order. Composite
certificates are retained. For every certified prime candidate, exact
order, square condition, lift and both full Hctrl routes are verified.
The candidate is admissible iff order>2, B^2!=1, valuation_one and its
Hctrl unit are all true. All spacing/prime-above-d requirements are already
fixed and independently checked. Stop at the FIRST admissible candidate.
No earlier admissible trial, omitted m, continuation after success or
shortened exhaustion is allowed by the full prefix validator.

`found` selects exactly that final m and sets
conditional_premises_discharged=True. `bounded-exhaustion` requires ALL64
trials, no admissible candidate, selection None and that Boolean False.
Both negative outcomes are scientific results, not verification failures.
All statuses are exact canonical spellings, with no unknown-case fallback.
No claim about candidates outside the interval follows from exhaustion.

If found, the complete certificates discharge exactly the finite premises
of section8 of the accepted conditional native adapter: odd prime lambda>d,
228956|lambda-1, three square conditions, first lambda lift and Hctrl
units at53/8807/lambda. The retained ordinary proof then supplies its
cofinal actual-rank construction and both positive native/Pell maps.
It still does not materialize or verify a numeric four-port53 tuple,
new specialized DAG, endpoint or printed page. Those are separate tasks.

## 6. Actual semantic controls and immutability

Seven private ACTUAL Phi models alter a tile coordinate/order/type,
dummy/control coefficient or old K low bit/minimal encoding. They must
reach their specific full-coefficient, field or exact-division rejection.
Two valid Phi models reverse control order and split a positive coefficient.
They traverse the full same coefficient verification without new modular
evaluation. No parent bytes are changed.

Nine actual fixed53 certificate models corrupt the trial bound/prime
classification/integer type, exact order/factor/proper-power witness,
square flag or bracket residue/unit flag. They call the same validators
against the unchanged independent positive certificate. Three actual
scientific reports corrupt outcome, selected m or the discharged flag.
Their validators must reject the exact semantic inconsistency. Valid
factor/witness permutation and complete typed JSON round-trip are retained.
Thus19 negative/four valid controls ALWAYS run.

If a prime lambda ACTUALLY occurs in the tested prefix, three lift controls
alter its modulus/residue/valuation flag and a fourth changes its m. They
must fail at the named schema/power/predicate location, giving23 negatives.
If that branch is absent, the receipt explicitly reports it unexercised;
no fake prime or extra candidate is introduced to inflate test coverage.
The complete actual model/certificates/cache are compared with their
saved copies after all controls. Explicit exceptions/counts survive-O.

## 7. Authentication, I/O and retained scope

The standalone runtime imports only standard-library modules, disabling
bytecode writes before further imports. Whole held membership/own pins,
all flat direct records, six complete parent inventories/member records,
the entire read-only old65 template and physical Python bytes/resolution
authenticate BEFORE arithmetic and again before writing. Strict JSON
rejects duplicates/nonfinite values. Records and mathematical schemas
reject Boolean/float integer impersonation; safe relative paths reject
traversal and symlinks. All accepted ordinary53 review pairs and joint
acceptance, full943 table and old four-port association are bound.

Only one selected fixed absent/tmp JSON is written exclusively and printed
in full as stdout. Mode-specific first/fresh paths are checked before work
and immediately before the write. Twelve JSON/stdout/stderr capture paths
are fixed by TOOLCHAIN; no held/parent/source/data/page path is an output.
Reports omit timestamps, duration, PID, output path and first/fresh ordinal,
allowing whole same-mode deterministic replay. No metadata is added to this
held folder after execution. Evidence closure needs separate authority.

No adopted source application, producer/checker, prime library, decoder,
native/compiler/Lean/TeX/PDF code is imported or called. Parent native/source/
Pell/K215/refutation and foundational contracts are retained ordinary
mathematics, not freshly rerun here. Verification PASS is exactly source/
route/certificate/control/integrity success, never scientific existence
by assertion, a consistency decision, new tuple, size saving or optimum.
