# Complete complemented-label radix47 specialization

This component specializes both new 85-operation, degree-232 graphs to the
entire previously calibrated complemented-label radix47 tuple. It is a
separate polynomial specialization, not a change of notation for the
radix67 polynomials. All four fixed ports change together.

The late archive comparison in `../LATE_COMPARISON.json` establishes that
the 85/232 bV graph itself is already present upstream. It also records a
separately calibrated one-anchor7309 tuple at 172011 raw bytes, smaller
than this whole47 tuple, and the archive's report of a still smaller latest
repository display. No new85/232 metric point or coefficient-storage
record is claimed here. The b² carrier refinement and its separately
checked whole-tuple specialization are the scoped contributions.

The new transport proof is `../PROOF.md`. The existing inverse-correction
specialization is retained as `inherited/inverse_binding_proof164.md`.
The full native bridge is `inherited/native_bridge149.md`. The actual
ordinary carry/controller proof is retained at
`inherited/provenance/radix47/radix47/radix47_proof.md`, with SHA-256
`3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224`.
The last hash is the one explicitly identified by the native bridge.
The retained coefficient array, all 51 target identities, and native P66
polynomial also match the bridge's original pinned hashes exactly.

## 1. What is changed

Use the complete formula in `../PROOF.md` with this whole four-port tuple.
The independent variables, domain, all 85 gates, the two choices L=b² or
L=bV, and the exact degree proof remain unchanged. This tuple has

    beta=2^413929-1,
    largest fixed port =415904 bits,
    total raw coefficient bytes =207214.

Its full finite coefficient definition is printed in
`coefficient_recipe.tex`; the literal 436-character seed, 430 decoded
actions, 943 tiles and all 3297 coefficients are implemented in
`inherited/rebuild_coefficients_149.py`.

This is the complemented-label tuple, with all 34 physical edge-label bits
complemented and seven shared marker weights. It is not the separately
discussed conditional47 three-anchor layout, nor the old67 tuple with its
radix symbol changed. The source mask MF is shifted by beta exactly once.
The native controller uses the actual new K0 and prime 1012691.

## 2. Why the arithmetic proof transfers

The new argument in `../PROOF.md` uses the port bounds

    beta>=31 odd, K0>0, 0<MC<beta<MF<2beta

before its native handoff. The rank estimate and parity/half-binomial
handoff additionally use the established mask phase and population facts.
The whole47 native bridge proves these for its actual tuple:

    MC=2 mod4, MF_native=4 mod8,
    pc(MC)=413929-986, pc(MF_native)=986.

It also proves the whole changed carry/decoder theorem and constructive
controller, rather than importing the old67 decoder. The inverse
specialization in package164 explicitly composes these interfaces with
the inverse cubic. The unsquared trace and new b² transport proof change
only the auxiliary Pell/carrier argument: their estimates and congruences
are uniform in the four fixed ports. They do not use the numeral 67.

Thus a positive zero of either new whole47 graph gives exactly

    C>0, q=beta J+1, X=qw=2^R, q³|Y, R=3 mod4,
    Y equal to the native half-binomial,
    (K0+w)C-F=t(q-1), t>=0 integral.

These are the whole47 bridge's native outer premises with Wbase=w.
Set z_source=t+1. Its source transport is then exactly

    (K0+w)C+(q-F)-z_source(q-1)=1.

The bridge reconstructs fresh source Pell witnesses at
A_source=Y(X+1)+2, not at our auxiliary A=Y(X+1)+1. It verifies every
factor of the actual whole47 P66 polynomial. Its uniform source recovery
then invokes the changed complemented-label decoder and produces a finite
syntactic ZFC refutation. No old67 decoder or arbitrary numerical-port box
is being substituted for that bridge.

## 3. Positive completeness uses the new controller

A finite refutation is supplied to the whole47 controller. The complete
native proof supplies actual q=2^a, X=2^R=q W_native, R>3q,
R=3 mod4, q³|Y, C>0 and t>=0 with the precise new transport relation.
Choose w=W_native and s=Y/q. These are positive integers, and the coefficient
of C in B is exactly K0+W_native.

The same scale-one Pell construction, positive period seed and unsquared
trace completeness then give positive eta,zeta,i,T and positive V,y.
The inverse-correction argument proves rho integral, including its
projection-before-denominator order. The explicit weight-independent bound

    g>kappa+sigma+|rho|

makes n=gy+(1+hL)t+rho-kappa-sigma a strictly positive integer for either
L=b² or L=bV. The carrier is z=gy and the polynomial vanishes.

This proves both existential directions using the new whole47 controller.
It does not assert a pointwise equality or witness bijection between the
radix67 and radix47 specialized polynomials.

## 4. Verification and scope

`build.py --check` freshly reconstructs the whole tuple and compares all
raw and compressed payload hashes. Its retained recipe checks every one of
the 3297 coefficients, all 51 native target identities, mask populations
and phases, carry bounds, controller primes, exact multiplicative orders,
and the valuation-one lift using the actual new K0.

The independent specialization verifier requires the complete native P66
binding and exact free-port gate equality with the new generic companions.
It then performs 36 exact polynomial cuts, the full highest homogeneous
component check, liveness/count checks, payload checks, and 22 operator
corruptions per graph. These finite checks supplement the explicit native
and arithmetic proofs; they do not replace them.

For either actual polynomial, the ordinary proof composed with those
named inherited calibrations proves in ZFC that positive unsolvability is
equivalent to Con(ZFC). No new complete Lean/Rocq closure, proof of
consistency, global optimum, or new native encoding is claimed. The radix47
coefficient reduction itself belongs to the retained predecessor; this
component contributes its checked composition with the new 85/232 forms.
