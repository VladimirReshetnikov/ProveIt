# Independent semantic review of the 1064921-bit radix exponent

Reviewed `coefficients/COEFFICIENT_PROOF.md`, the literal new coefficient
payloads, and the source mixed-field, parity-track and unrounded-controller
proofs, at the stated 8c6eec9d19ef80538c8e61ff6e0180040583446a pin.

## Decoder and geometry

The low ten bits of each clause sum count selected tiles modulo1024.
There are only943 tile selectors, so masking1022 permits exactly count0
or1, without assuming higher payload fields are carry-free. After this
count conclusion, each payload field has only two Boolean contributions;
the radix4 fields therefore cannot carry. The support identities include
both reflected clause terms. They establish the required copy equations
for every native assignment by linearity, not merely for valid tilings.
The independent raw-payload decoder checks all those identities.

The two reflected-clause supports are disjoint modulo8801, and the two
anchor supports intersect only at0. Together with the inherited binary
rotation lemma and the proved carry/slack bounds, these give the same
local decoding and whole-cell temporal alignment as the old compiler.
The new zero tests lie strictly above every aligned convolution exponent,
so they are redundant for completeness; dropping them leaves the old
soundness implications. Their contribution to mask populations is real
and is used explicitly in the parity proof.

## Controller

The factorization d=11^2*13*677 and order ord_d(B)=780 are used at the
full modulus, not merely modulo its squarefree part. The controller
lambda=2341 satisfies lambda=1 modulo780, so lambda-power widths and
areas make q and B^width congruent to B modulo d. Modulo lambda the
same conclusion follows from Fermat. The recorded unit checks at the
four primes therefore imply gcd(Gamma,dN)=1, including the full11^2
factor and every lambda power.

The non-Wieferich certificate gives order lambda^(n-1) for B^(lambda-1)
modulo lambda^n. Its simultaneous residue modulo d is1. CRT then identifies
the orbit exactly with 1+d*lambda*z, z modulo T=lambda^(n-1).
The added B^3 cell is essential: after normalizing by B^2, choosing whether
to include it makes the desired residue nonzero modulo lambda. Its least
residue a modulo d*lambda is positive, below T, and invertible modulo T.
The consecutive-coordinate subset construction then covers every residue
modulo dN. It does not assume every residue is itself a unit. The positions
2+(lambda-1)j are distinct and exclude3. The bound width<T guarantees
that each selected position and its required translates by1 and width
stay below N. Thus the dummy changes used in the rank argument are legal
and preserve the unique Start and all mask tests.

Completeness may choose arbitrarily large lambda-power widths and heights:
the unchanged tile language pads finite computations with untouched blank
margins and repeated halting rows. These are independent padding directions;
no parity or fixed ratio between width and height is required. Soundness
does not impose any prime-power condition on a recovered solution.

## Canonical witnesses and transfer

The population identity pc(R)=3t+2 uses actual mask populations, disjoint
acceptance bits, and the exact two-block rank decomposition. Both d and
N are odd, and R=3 modulo4 is unaffected by high dummy changes. Therefore
X/q=2^(R-t) is a positive square. The inherited strong-Pell parity argument
uses only the odd rank and even Pell base; it does not require t to be a
power of five. The authentic half-binomial valuation then gives an odd
cubic scale s. These are precisely the extra canonical promises used by
the signed source families. No transfer is based only on congruences:
the decoder, controller, padding and strict slack arguments above precede it.

The new four ports are a coherent replacement of the ordinary compiler
interface. The quartic31 transfer is its exact positive-zero-set elimination;
all downstream Jones weighted coefficients and index constants must be
regenerated from that newly instantiated quartic. Keeping old Jones y or
weighted coefficients while changing the ports would not be justified.

## Evidence boundary

`COEFFICIENT_DECODER_REPLAY.json` records a replay of the separately authored
raw decoder, not execution of an upstream program. Its numerical checks
supplement the universal argument above. The source native/Pell and K215
calibration theorems remain inherited mathematical dependencies. No new
Lean/Rocq certificate or proof of Con(ZFC) is asserted.
