# Independent review of the 5,263-tile coefficient adapter

Reviewed `REFINED_COMPILER_PROOF.md`, `compiler5263.py`, `T5263_CONSTANTS.json`,
the inherited T4 bridge audit, and the blank helical proof's actual-rank
tuning section. The review concerns correctness of the changed interface,
including completeness and the parity refinements; it is not another run
of the exhaustive enumerator or a new formal proof of the inherited compiler.

## Conclusion

No substantive defect was found. The new coefficient tuple supports the
twelve-positive-variable reduction and the odd-scale 27-integer reduction,
and consequently their 26-integer combination, under the inherited
compiler/Pell theorems. It is essential to replace all four ports together
and retain the shifted high-mask port `MF_native+B-1`.

## Local language and completeness

The code's `valid` predicate is the old T4 predicate with additional local
filters, except for the deliberately retained old forbidden tile. Soundness
therefore transfers by inclusion. That forbidden tile still cannot occur
globally: its left H cell would have a non-V right neighbor 0.

The new filters hold on an actual finite computation after padding with at
least two untouched blank headless cells on each side. Requiring every head
in a triple preceding H to be halted is satisfied by an absorbing halted
tail. At a helical seam the time-independent V separates the differing time
coordinates. The immediate phase neighbors can be R and L respectively;
all ordinary cells within distance two remain blank and headless. Thus the
filters do not destroy the independent large width and height choices.

The closed tile count was checked independently from the stated cases:
1751 and 1744 for ordinary headless centers, 1720 for working heads, 16 for
halted heads, 5 each for L and R, one Q, nine V, and twelve H, totaling 5263.
Start's next-center symbol is correctly 1 under the literal first action.

## Layout, carry, and rotations

The compact copy offsets are consistent with the three exact overlap tests.
In particular the changed shift 878 sends the next-copy interval to the
center-copy interval; using the old shift 1317 here would have been wrong.
The shift Hc+439 and the spatial coefficient rho^Hc give the two horizontal
tests. The two anchor shifts retain the unique pairs (M,9M) and (3M,27M).

The support has 7024 positions, including one dummy. The upper dummy
position 7020 is strictly below the first anchor 7021. Nonanchor support
therefore cannot introduce another pair with difference 18M. The band
separation is exactly 2Emax+4, and T2+2Emax+2<Lcell. These are the strict
separations required for the inherited all-rotation proof, including the
upper-dummy spill case, rather than merely an unrotated layout check.

The recomputed radix bounds are sufficient: b=78125 exceeds bmin=36936,
and both the mu and carry masses fit far below rho. A=8192 exceeds k+1.
The support, coefficient fields, and population formulas agree between the
proof, generator, and JSON recipe.

## Actual packed-rank tuning

This is the main completeness check. The old residue 3 of 2DC-DR is not
an invariant that must be preserved; the proof needs it to be a unit.
For the new layout, paired clause bands cancel modulo five, and the four
bare exponents give DC=2 modulo five. Also DR=2 modulo five. Thus

    2DC-DR=2 modulo five.

With width and height powers of five, B, B^width, and q are all 2 modulo
five. In the exact low-dummy increment

    delta R=-Gamma B^j,
    Gamma=rho^7019 (q^2-1)[1+q(DC+B DR+B^width)],

the bracket is therefore 2 modulo five. The other factors are each 3
modulo five, giving Gamma=3 modulo five. It is invertible modulo dN,
which is a power of five.

Consequently the inherited Boolean subset lemma can still select the
residue (R0-d*width)*Gamma^(-1) modulo dN, tuning the actual final packed
rank to R=d*width modulo dN. This does not replace the packed rank by a
freely chosen exponent. The low dummy changes remain linear in C and F;
the original uniform carry bound permits their simultaneous use. Height
at least 25 and N>25d ensure j+1<N and j+width<N for the stated subset
positions. The strengthened local filters still permit these size choices.

Start remains selector zero, the excluded tile remains selector one, and
all copy/dummy positions have positive exponent. Thus the canonical origin
high-mask test and positivity of the outer slack/transport witnesses survive.

## Compatibility with odd s, square w, and the H-divisible multiplier

The mask census gives

    pc(MC)=d-7024, pc(MF_native)=7024,
    MC=2 modulo four, MF_native=4 modulo eight.

The omitted selector-one bit and the upper-dummy deletion give the stated
low-mask population; the two mu bands, three overlap groups, two anchor
targets, and bit two give the stated high-mask population without overlap.

These are precisely the invariants needed by the odd-s population proof.
For q=2^t, the repeated-mask identity gives pc(Tmask)=t+2, and the disjoint
native-mask blocks give pc(R)=3t+2. The unchanged half-binomial identity
then yields v2(Y)=3t, so s=Y/q^3 is odd. Dummy tuning preserves those native
mask tests and therefore does not lose the population identity.

The canonical Start gives C=1 modulo four. All dummy changes occur at
higher binary positions, so the actual packed rank remains R=3 modulo
four. Since d and N are powers of five, t=dN is odd. Hence R-t is even,
and the canonical w=2^(R-t) is a square. The tuning lower bound guarantees
that the exponent is positive.

Finally the twelve-variable construction changes the later strong Pell
index, making its normalized multiplier divisible by the arithmetic H.
That operation leaves the compiled tableau, q, R, s, and w unchanged.
Therefore it remains compatible with the new coefficient tuple and with
the odd-s and square-w choices. No oddness condition is imposed on the
new H-divisible multiplier in the 26-integer construction.

## Scope

This review validates the adapter against the explicitly stated inherited
mathematical interface. The general Boolean subset lemma, native compiler,
Pell extraction, and K215 calibration remain substantive inherited proof
dependencies. Finite tile and geometry checks do not by themselves prove
those universal theorems. No new Lean/Rocq build or internal ZFC derivation
is asserted here.
