# Independent review of the complete single-dummy4027 tuple

Reviewer: `/root/controller_certificate`. Proof author:
`/root/complemented47_review`; finite probe/certificate author:
`/root/circuit_reduction`; ROOT coordinates the candidate. This reviewer
did not edit the reviewed proof, verifier, probe or finite artifacts.

**Result: PASS within the stated ordinary-proof boundary.** I read the
entire proof, README, probe note, final verifier and exploratory verifier,
then ran both programs in normal and optimized Python modes. All four
read-only runs reproduced their exact stored artifacts. I found no gap
in the changed carry, phase, mask, rank, safe-subset or controller argument.
The later Boolean-only-dummy proposal is a different tuple and is outside
this review.

## Exact reviewed bindings

All paths below are relative to `Computability/DiophantineConsistency`.

| Artifact | SHA256 |
|---|---|
| `research/single-dummy-independent/PROOF.md` | `a8b695c016263a3ac98851c1b54e2adb66b8254e49af2ec1447d91a3e01da638` |
| `research/single-dummy-independent/README.md` | `b92d94e61cc00d9b9572702b62a94acc5e0cf3fec8a3caecd39dff9afde9e34f` |
| `research/single-dummy-independent/certify.py` | `0c1e55958f20b3e0cbcd3e27488f0dadfafc23456d2c20ab8ef5eec60df09530` |
| `research/single-dummy-independent/certificate.json` | `bff400f62a90830a82dfcad43605560224efe08555b17be012d036462cd55500` |
| `research/single-dummy-independent/coefficients.json` | `485f3e3bfa617cb5a1b7aa98447d3629b8e53057d0f2aed5eecb56fd6b52ac98` |
| `research/merged-copy-one-dummy-probe/probe.py` | `bb40578e8ee47d8c2bf63580abebc365a73f82014484eb4385e459c11856e1a5` |
| `research/merged-copy-one-dummy-probe/RESULTS.json` | `3095bad3bb0d7ca3c4dda3b38c73bb5641b16248a25cb878505545d602231b62` |
| `research/merged-copy-one-dummy-probe/COEFFICIENTS.json` | `a1f2811d1a52ee03fb25e31c79c0d8127c97bc9396eaa3b8c9c640a321af120d` |
| `research/merged-copy-one-dummy-probe/NOTE.md` | `04d6ebe164c5f3118fc7ad14c847604eb69e3b9996fe11a07ee86c5664beeaf9` |

The exact preserved decoder/helper chain was reviewed previously and is
checked by the verifier before import. In particular its one-anchor7309
parent is `9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`;
the complete finite language is the pinned radix55 page
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The new verifier pins the entire new proof and uses explicit exceptions,
so `python -O` does not disable its checks. Its default mode is read-only;
neither reviewer run used `--write`.

## Ordinary proof audit

The new support has 979 positions, comprising 977 weighted positions,
the low dummy978 and the zero-weight marker1006. The dummy allows0..3;
position979 is an existing weighted east label, not a second dummy.
The mask clears978 ordinary physical bits, excepting selector1, plus
the extra bit at978. Thus its population is `d-979`. The 105-bit core
and874-bit padding give native population979. The source-mask shift is
exactly one beta. The origin changes still give actual mask populations
`(d-979)N+1` and `979N+1`, hence the same `pc(R)=3t+2` and `R=3 mod4`.

The one shared bare18 term occurs once. All17 copy identities, the marker
copy, both clauses1994/3001 and their complete predecessors1993/3000
match the full convolution. Gap1007 excludes foreign clause terms;
gap-minus-one1006 has just the pair marker1006/selector0. The upper
predecessor therefore has precisely the extra `c0*x1006`.

The global carry argument allows the sole dummy's full0..3 range. Its
extra0/2 contributes at three distinct bare/spatial outputs, all below
the first reflected dummy output1986. A reflected coefficient cannot
hit through both clause bands. The global29 bound is valid. At fractional
phase46 the dummy's only odd spill lands at979; the weighted label's own
contribution there is even and the sum is at most `rho/2+1`, with no further
spill. This preserves the physical support required for a clean clause.
The clean clause recovers at most one selector before alignment is used.

The low region resets carry before the eight Start south tests and the
marker test. Fractional phases1..45 have no odd temporal digit and46 has
at most one; neither can satisfy the tests. Of the remaining field offsets,
20 forces selector942 and an incompatible south bit0. The whole retained
tile942 has complemented south74. Offsets21..962 force two selectors in
one cell. The parity relation then identifies the marker with the shifted
Start indicator. Occupation follows from positive complemented colors,
without an earlier assumption that the marker is always one.

The changed adjacency is explicitly included: the extra dummy value can
add `2*c979=2048`, giving `Aadj<=2M+1024`. Adding `c0` and carry29 remains
below rho. Both clause predecessors reset. The last product4007 is exactly
`c0*x1006`; every later field through4026 is zero after that reset. All874
padding bits are therefore valid, including the28 low bits at4026.
The strict canonical bounds and all safe Boolean dummy subsets follow.

The ordinary safe increment has maximum local/spatial/temporal exponents
3979/987/978. The proof avoids coefficient collisions and physical wrap;
the degree-plus-one margins imply the three-term bound below `q/rho^2`.
Strict representative slack then gives an ordinary equality for deltaF,
and subtraction of the actual rank gives the stated deltaR. The controller
uses the new K and new dummy exponent978. Its orbit/subset proof and both
full positive P66 witness maps are restated and remain valid. The uniform
66-operation integer circuit and exact degree157 are inherited symbolically
at the new four ports, not by asserting equality with the old specialized
polynomial.

## Independent finite reconstruction

In addition to rerunning both reviewed programs, I authored and fully read
a temporary stdlib-only reconstruction that imported no project module.
It retained the already reviewed943 selector coefficients, rebuilt all
new labels and zeros, and compared all3297 coefficients. It independently
formed the physical support and kernel, checked every copy, clause and
predecessor, exhausted all4027 residue offsets, reconstructed every full
integer port and its byte hash, and checked primes/orders by trial division
and all prime-factor proper-order tests. The retained selector coefficient
itself independently decodes the needed tile942 south74 calibration.
This supplementary run is an independent check of the changed layout;
the original complete seed/decoder provenance remains provided by the
pinned, rerun full verifier.

The935 support offsets split into zero,933 multiple-selector exclusions
and the exceptional offset20. The Boolean adjacency bound is
32607504957441. The full extra-dummy convolution maximum is
3836048195695509 at field2540 and satisfies the stated global carry bound.
The exact phase46 dummy/east-label possibilities were separately checked.
The verifier's marker-deletion negative control rejects the population
and physical geometry even though its coefficient is zero. Its local
marker1005/offset19 example is correctly scoped as a local phase-test
counterpattern, not a complete native witness or a global minimality proof.

`L=4027` and `d=189269`; exact orders of2 andB are23 modulo47 and1342
modulo4027. The latter order factors as `2*11*61`, all proper-order tests
pass, and both orders are coprime to d. The spacing is30866. The auxiliary
prime is `lambda=246929=8*30866+1>d`.

| modulus | B | K | B squared | H |
|---|---:|---:|---:|---:|
|47|4|12|16|18|
|4027|3596|836|519|2634|
|246929|104077|54603|234415|79912|

The valuation-one lift is
`B^(lambda-1) mod lambda^2 = 45579142537 = 1+246929*184584`.
All required H values and `B^2-1` are units. The exact four raw ports are:

| Port | Bytes | SHA256 |
|---|---:|---|
| beta |23659|`236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70`|
| K |23712|`506ba903a9ca9db6d51be2bce05bd9b906d0ceb7cf94cfaf094a28b99f0d5790`|
| MC |23659|`33bc65bace7f8d7c281a9a5c27ff0c741af4e4c5179e29e501618d430cf25908`|
| MF_source |23659|`8dcd4049c011cabd366a91458eca7463bee5ab06b9aecbedfc152ad4e14de7ad`|

Total94689 bytes:516 below the complete4049 tuple and2357 below4127.
This review establishes no printed-page size, global minimum, actual
unsolvability, or new formal-kernel/internal-ZFC replay. The complete
ordinary equivalence remains relative to the explicit retained arithmetic,
syntactic-refutation and foundational contracts. The new finite Pcsd18
premise is discharged for the exact tuple reviewed here.
