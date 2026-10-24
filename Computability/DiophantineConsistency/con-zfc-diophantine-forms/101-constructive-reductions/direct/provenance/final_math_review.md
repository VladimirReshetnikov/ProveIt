# Final mathematical review of the synchronized direct construction

## Scope and conclusion

This review concerns the ordinary mathematical composition producing the
frozen natural quartic: **522 nonnegative integer variables, 400 quadratic
residuals, 20,225 collected monomials, degree four**, with maximum absolute
expanded coefficient **83,900,628**. I inspected the synchronized builder,
the shared-power/index proofs and exact audits, the frozen literal census,
the contraction verification receipt, and the immediate logical calibration
sources. The final composition was reviewed separately from the report and
contraction authoring; the reviewer also authored the shared-Pell modules,
so this is not external peer review of every component.

I found no mathematical obstruction in the synchronized frame, simultaneous
index witnesses, or deferred binomial radix. Their strongest potential gaps
are addressed below. The finite audits corroborate the emitted identities;
the universal proofs, rather than the test cases, establish correctness for
unbounded witnesses. The domain is essential: the 522-variable equation is
over the nonnegative integers. It must not be read as an unrestricted-integer
equation without the separate domain conversion.

## Global Pell frame: the missing bound cannot be assumed

The weak estimate A>W^2 alone would not bound n^k for arbitrary n,k<=W.
The argument needs the additional Pell-index divisibility. From

    A^2-W^3(W+2)(z+1)^2=1,

standard Pell-solution classification gives A=X_j(W+1) and
W(z+1)=Y_j(W+1). The recurrence modulo W gives Y_j(W+1)=j mod W.
Thus W divides j, and positivity of z+1 gives j>=W. Consequently
A>W^W>=n^k. The modulus T_n=2An-n^2-1 is at least 2A-2, so both the
proposed m<=W and true n^k are strictly below T_n.

The recurrence identity H_(r+1)=n H_r+T_n Y_r, with
H_r=X_r(A)-(A-n)Y_r(A), proves the required congruence and the nonnegative
quotient orientation. Equality follows from the strict modulus bounds.
This supplies an independent ordinary proof of the power graph, without
requiring the entire inherited positive-power theorem.

Exponent positivity must hold before this argument. The final construction
provides it by its actual addition/multiplication syntax. Base positivity is
forced by 2An=T_n+n^2+1, since n=0 is impossible over naturals. Hence using a
factorial output as a base does not make power correctness depend circularly
on already knowing factorial correctness.

Completeness does not choose local Pell witnesses and then silently identify
them. It first fixes the intended finite semantic values, sets
W=2+sum(distinct base/exponent/output atoms), and explicitly chooses
A=X_W(W+1), z+1=Y_W(W+1)/W. The quotient is a positive integer.

## A common auxiliary index certificate really exists

Sharing U,V,B would be invalid without a simultaneous extension argument.
Let the true positive index coordinates be Y_i and put
L=4 product_i Y_i^2. The element A+s is a unit in the finite ring
(Z/LZ)[s]/(s^2-(A^2-1)), with inverse A-s. A positive power is therefore 1.
Its Pell coordinates give U=1 mod L and V=0 mod L, V>0.

In particular U is odd, and the Pell norm implies gcd(U,V)=1. CRT can now
choose B=A mod U and B=1 mod 4V, then raise B above A. Thus the strengthened
relations V=(product_i Y_i^2)(v+1) and B=1+4V(q+1) have simultaneous natural
witnesses. The individual S_i=X_ki(B), R_i=Y_ki(B) have the required
congruences and nonnegative quotient signs. Conversely, these stronger
relations restore every individual index certificate; no reverse CRT
assumption is needed in soundness.

## Deferred common binomial radix: auxiliary cycles are harmless here

The shared radix is q=2^K+1, where K is the sum of the distinct binomial
upper-argument atoms. For each upper n, n<=K and every binomial coefficient
is at most 2^n<q. Therefore the q-adic expansion of (q+1)^n is carry-free,
and the actual quotient/remainder equations isolate binom(n,k), including
the case k>n. This reasoning applies simultaneously to every satisfying
assignment; it does not assume that earlier binomial outputs were already
correct when q was defined.

For completeness, evaluate the original acyclic circuit with genuine
binomial/factorial operations first, and only afterward choose its auxiliary
q and digit witnesses. In soundness the power graphs are proved correct
first using their syntactically positive exponents; then all digit graphs
are identified; the original semantic macro dependency order can finally
be used. This order avoids an appeal to correctness through a cyclic
auxiliary definition.

The local bounding order also remains valid: choose the finite C222
derivation and m bounding all seven Horn coordinates, then its carrier and
accumulator states, then y bounding the states, and finally the beta code x.
The quotients are automatically <=x. Bounding states by y makes them
strictly smaller than 1+(i+1)y, so deleting the two local remainder slacks
does not discard a necessary canonical-remainder condition.

## Calibration and the precise meaning of “no K215 simulation”

I read the complete immediate copies of `KEndpoint.lean` and
`ConstructibleChoice.lean`, whose SHA-256 values agree with
`CALIBRATION_PINS.json` at commit
`08200eb10fde2db408c69dffd840d6920a569b1f`.

`KEndpoint.c222_iff_zf_refutation` is an unconditional theorem

    KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot.

It occurs before the file's machine-parameter section. Its proof combines
`KUpper222.zf_refutation_of_c222` with the semantic lower chain through
`KEind222.c222_complete`, seed constructions, and ZF model existence.
It has no machine, tape, simulation, boot, coverage, or halting hypothesis.
The same module imports machine helpers and later proves separate halting
theorems; those later theorems are not used by the present calibration.

`ConstructibleChoice.zf_refutation_iff_zfc_refutation` then uses theory
inclusion in one direction and the constructible model of ZFC, first-order
soundness, and completeness in the other. Its proof has no machine input.
Thus “the equation does not encode or simulate K215” is accurate. The
stronger statement “its source import graph contains no machine-related
modules” would be inaccurate and should not be made. This review checks
these immediate theorem bodies and interfaces, not a fresh kernel rebuild
of their full transitive dependency graph.

## What is established about ZFC

The intended conclusion is the ordinary mathematical theorem

    ZFC proves: (there is no natural zero of the supplied polynomial)
                <-> Con(ZFC),

where consistency is tied to the inherited sealed syntactic refutation
predicate. The new arguments are uniform finite arithmetic, CRT, natural
induction, polynomial identities, and finite Pell arguments; they do not
restrict certificates to externally standard naturals or assume arithmetic
soundness or consistency of ZFC. Together with the inherited ordinary
calibration and the checked literal substitution identities, they supply
an argument formalizable in ZFC.

No new Lean theorem for the complete generated polynomial, and no sealed
object-language ZFC derivation, is supplied. Existing external Lean
calibration declarations are not themselves such a new proof object.
The work also does not prove that the polynomial has no zero, prove
Con(ZFC), or establish global minimality of the equation. Its concrete
achievement is a substantially smaller materialized direct quartic with
an ordinary proof of the requested consistency equivalence.
