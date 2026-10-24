# Independent audit of the direct Laurent majorant

Audited against the candidate's `radical_bound.json`, SHA256
`e268598e0443868226c944bb10fad9f31bb9d335312ae0d6d3e2a61b577294d9`,
and ProveIt package 71 at commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37`.

**Final conclusion:** the polynomial P itself is a strict majorant; no
correction term is needed. Its final equation has exact degree 1,158,228.
The complete defect-positivity certificate below supersedes the earlier
absolute-mass correction.

The independent script `audit_laurent_majorant.py` uses an integer sparse
ring implemented directly with four-tuples. It imports no construction
algorithm and no symbolic algebra library. It checks all 654 coefficients
of P through the complete defect identity, the 3,781 defect coefficients,
all 1,816 coefficients of the shifted P certificate, all 32,637 coefficients
of the shifted defect certificate, the entire top A-degree block, and the
exact outer weighted-degree comparisons.

## 1. Uniform polynomial majorant without a correction: accepted

Use the candidate's D,F,G,H,I and Q=DFI in indeterminates A,C,i,Z. Put
sigma=65536 C^7. The independently reconstructed identity is

    P^2-sigma^2 Q = Rdefect.

Every exponent in P is nonnegative. The defect has component degrees at
most (22,42,10,2), and its absolute coefficient mass is

    S=140213210301297074855.

Consequently, for A,C,i,Z>=1,

    |Rdefect| <= S A^22 C^42 i^10 Z^2.

The polynomial P(A+3,C+1,i,Z) has exactly 1,816 nonzero coefficients,
all strictly positive. Its complete top A-degree block is

    2^26 A^23 (C+1)^31 i^5 Z.

Its constant term is positive when i,Z>=1, so P>0 for A>=3,C,i,Z>=1.
More decisively, the entire shifted defect

    Rdefect(A+3,C+1,i+1,Z+1)

has exactly **32,637 nonzero coefficients, all strictly positive**. Its
constant coefficient is

    295870595720775501924817 > 0.

Thus Rdefect>0 on every boundary of A>=3,C,i,Z>=1, including A=3 or any
of C,i,Z equal to1. Consequently

    P > sigma sqrt(DFI) > 0.

This is a finite exact algebraic certificate for a universal inequality,
not a sampling test or an asymptotic approximation. No absolute-mass
correction is required in the final equation.

## 2. Earlier correction bounds: optional, superseded

The following bounds were independently checked during the research, but
are not part of the final equation. They explain why the final
positivity certificate gives a cleaner result.

The complete top A-degree block above proves

    P >= 2^26 (A-3)^23 C^31 i^5 Z
      >= 8 A^23 C^31 i^5 Z                 (A>=6).

Together with the absolute-mass bound, this would suffice for a correction
B=(S+1)C^11 i^5 Z. Using only the isolated shifted C^31 monomial would
give (C-1)^31 and fail at C=1; the entire binomial block was checked.

For the actual source, Z=2Rsource+1+(j-1)C with j>=1. Also

    A=Rsource Y(U+1) >= 2Rsource,

since U,Y>=1. Put t=(j-1)C>=0 and L0=2+t>0. Then

    Z=2Rsource+1+t <= A+1+t <= A(2+t)=A L0.

Therefore the smaller correction

    Bnew=(S+1)C^11 i^5[2+(j-1)C]

still gives

    2P Bnew
      >=16(S+1) A^23 C^42 i^10 Z L0
      >=16(S+1) A^22 C^42 i^10 Z^2
      > |Rdefect|.

Thus the same strict majorant holds with Bnew. This substitution is proved
on the full positive source-input domain, before any zero equation or
packing claim. It is not based on source-zero restrictions. A>=6 follows
from the unchanged source's Rsource>=3 and U,Y>=1.

The source-specific correction has degree 18 after the outer substitution,
whereas the initial correction has degree 7,979. Both are unnecessary after
the exact four-variable defect positivity certificate.

## 3. Variable scaling is legitimate

The finalizer replaces the old radicand 4096^2 DFI by sigma^2 DFI,
where sigma=65536 C^7 is now a positive integer polynomial. This does not
change the ratio endpoint once the two square roots are extracted:

* The strict majorant makes the parenthesis in the real factorization
  positive, so the margin m is recovered as positive before integrality.
* The inherited margin estimates give C>K and C>B1+W1, hence the old
  scaled second radicand was greater than a0. Since sigma>=65536>4096,
  the new radicand is still greater than a0. The two-root rational
  extraction therefore has a nonzero denominator.
* The extracted second root u1 is rational and hence integral, since its
  square is the integer sigma^2 DFI. Then u1/sigma is a rational square
  root of the integer DFI, so it too is integral. No fixed-scale hypothesis
  is needed: sigma is evaluated at the current positive integer C and is
  nonzero.
* J divides Qratio exactly as before, because both extracted signed roots
  and both majorants are integers. There is no new denominator at this step.
* In completeness, a source zero supplies an integral root of DFI. Its
  multiple by sigma is integral, and the strict majorant gives the same
  positive formula for n. The source is unchanged.

These are the precise points where an unexamined replacement by a variable
scale could have failed; none requires the scale to be fixed independently
of the positive input tuple.

## 4. Exact degree: the delta0 P-squared term dominates

For source 71, deg A=16425, deg Rsource=deg Z=7963,
deg Omega=82360, deg E0=16429, deg V0=57239, deg delta0=57240,
and deg a0=114478. The relevant source leading coefficients are nonzero on
the actual fixed coefficient slice. Omega's leading coefficient is negative;
only its even powers occur in the degree argument below, so their leading
coefficients are positive.

For the final equation, V1=P and delta1=Rdefect. Their exact degrees are

    deg V1=385774, deg delta1=377328,
    deg Bsmall=2*82360+377328=542048.

The exact norm identity is

    F9=Bsmall^2+4Omega^2 V0 V1 Bsmall
                    +4Omega^4(delta0 V1^2+a0 delta1).

Its four degrees are respectively

    1084096, 1149781, 1158228, 821246.

Therefore the final exact degree is **1,158,228**. The unique largest
term is 4Omega^4 delta0 P^2. Its leading coefficient is positive, because
delta0=K^2-1 and the other displayed factors have positive leading
coefficients. Specializing the authentic positive fixed coefficients
cannot cancel this leader.

For comparison, with the discarded initial correction:

    deg V1=385774,
    deg delta1=393753,
    deg Bsmall=558473.

Its four degrees are 1116946,1166206,1158228,837671 respectively.
That preliminary corrected candidate's exact degree is 1,166,206,
not 1,116,946.
The mixed term has a positive leading coefficient and is uniquely largest.
The independent script checks these figures.

For Bnew the top monomial is (S+1) C^12 i^5 j and has degree18.
The top P monomial is 2^26 A^23 C^31 i^5 Z, so the leading cross-term
in delta1 is

    2^27(S+1) A^23 C^43 i^10 Z j,

of weighted degree385792. It strictly dominates the defect's maximum
degree377328 and Bnew^2 of degree36. Consequently

    deg delta1=385792,
    deg Bsmall=2*82360+385792=550512.

The four norm terms then have degrees

    1101024, 1158245, 1158228, 829710.

That second preliminary candidate has exact degree 1,158,245. The largest term exceeds its nearest
competitor by 17, so a certificate that ignores the mixed term is again
incorrect. All relevant leaders are positive; the specialization of the
fixed coefficients cannot cancel this unique leader.

## 5. Scope

The majorant algebra, bounds, variable-scale compatibility, and degree
calculations are accepted. The delivered literal DAG has also been checked
by `audit_laurent_dag.py`, independently of its generator. Its SHA256 is
`b7dae3927040c428146e0b7d2c2cb7590c99f1915a5b14c5471cb92ea4d5594c`.
The checker proves that 45 retained named source expressions are structurally
identical to package71, exactly reconstructs all 654 majorant coefficients
from the literal DAG, checks Z=B1+(j-1)C, and verifies the entire finalizer
as a polynomial identity with the new scale. It counts 1,753 live binary
operations: 923 multiplications, 810 additions, and 20 subtractions. Both
independent scripts pass normally and with Python optimization enabled.

The finite checker does not reprove the
native compiler, source-65 digit extraction, or the K215/refutation theorem.
Those remain the same explicitly inherited ordinary mathematical
dependencies as package71. No new kernel-certified internal-ZFC proof is
asserted by this audit.
