# Transport-coordinate clarification for Q45 and its Q37/Q34 reductions

## Finding and exact conventions

The transport display near the end of Section 4 of the preserved
`upstream/QUARTIC45_PROOF.md` mixes two coordinate conventions. The literal
polynomials are consistent: Q45 and its source Q50 use exactly the same
**shifted** coordinate `z`. Their transport residual, at zero-based index 13,
is

    (K0+w) C - F - z(q-1),
    q=beta J+1, C=q-F-alpha.                         (Tnew)

Expanding this expression gives the literal residual in both JSON packets.
In particular, Q45 did not change Q50's transport equation. Its first 23
arithmetic residuals are byte-for-byte identical as strings to Q50's; its
two retained eta/zeta guard residuals are also identical.

The older source uses an unshifted coordinate, here denoted `z_old`, with

    (K0+w) C + (q-F) - z_old(q-1) = 1.              (Told)

The exact coordinate change is

    z_old = z+1,
    (Told left side)-1 = (K0+w)C-F-z(q-1).

Thus the Q45 proof's display `(K0+w)C=(z-1)(q-1)+F` is correct only if
its `z` means `z_old`. Read consistently with the literal packet, that
display must instead be `(K0+w)C=z(q-1)+F`. Neither the Q45/Q50 JSON
packets nor any coefficient requires modification. No shift is applied
between Q45 and Q50. The Q37 and Q34 reductions retain this same shifted
coordinate and inherit the corrected argument below.

## Soundness of the new guards without assuming the missing z guard

Take an arbitrary integer zero of literal Q45. A sum of integer squares
vanishes only if every residual vanishes. Put

    Pos(x,y,t)=1+x^2+y^2+t(t+1).

The dyadic equation `beta J+1=2 q_half_root^2`, with the authentic
`beta=2^1064921-1`, gives `J>0` and `q>=16`: negative J would give a
negative left side, and J=0 would require 1 to be twice a square.
The two product guards give `F alpha>0` and `F C>0`. Hence F, alpha,
and C have the same nonzero sign; their sum q is positive, so all three
are positive. The retained guards give eta,zeta>0. Also
`s=2 v_scale+1` and `i=2r+1` are nonzero odd integers, and `w=u^2>=0`.
No sign of z has been assumed.

The unchanged arithmetic residuals restore

    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    a=(X+1)Y, c=kY+eta, H=4a+3,
    Delta=a^2+H, D=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, V=of-c=jc-R.

The source signed Pell recovery can be applied in its actual proof order,
before invoking the whole theorem that assumes z positive:

1. Since s is odd and q>=16, `|Y|>=q^3` and `|H|>1`. If w=0, then
   X=0 and the main norm reduces modulo H to `0=1`, impossible. Thus w>0
   and X>=q.
2. The positive simplex F,alpha,C supplies the source packing bounds
   `q(q^2-1)<R<q^4-2`, `R-2>3q+1`, and `|E|>=q^4>R+2`. These use
   the authentic mask bounds and C>0; no property of z is used.
3. The negative-scale proof in `ODD_SCALE_27_PROOF.md`, Sections 1--4,
   uses transport initially to infer C>=0 (C>0 for the system). That
   consequence is already available. Its remaining argument uses the
   displayed bounds, the first/main/strong/auxiliary Pell equations, and
   `V=-c (mod |f|)`, `V=-R (mod |c|)`, which follow directly from the
   exposed quotient equations. It never needs z again. The argument
   therefore excludes s<0 here and proves s>0.
4. The positive-scale signed recovery likewise uses the sign of z only
   in its initial inference of C>0. The bootstrap, ordinary strong-rank
   lemma, signed auxiliary index argument, and main-root argument then
   give `X=2^R` independently of transport. Signed i causes no problem:
   the strong equation uses i squared and its rank argument uses |i|.
   If the eliminated quotient T is needed, strong rank first gives
   `f^2=1 (mod c)`; then `of+R=(j+1)c` proves
   `T=(o+Rf)/c` is an integer and `c(Tf-1)-Rf^2=V`.

This dependency order is explicit in the preserved
`coefficients_source/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md`,
Section 6, and `coefficients_source/historical/DOMAIN_REDUCTION_PROOF.md`,
the section on soundness. The positive signed argument is also laid out
in `36-small-tuple/proofs/INHERITED_ORDINARY_PROOF.md`, Sections 3--6:
transport occurs in the initial C bound, while Sections 4--6 establish
the rank and X recovery without another occurrence of z. This is an
inspection of the hypotheses of the inherited argument, not an invocation
of the full source theorem before its z hypothesis is established.

Now `R>3q` and q>=16 give `2^R>q^2`, so

    w=X/q>q>F.

Since K0>=0 and C>=1, `(K0+w)C>F`. Applying the **literal** equation
(Tnew) gives `z(q-1)>0`, hence `z>0`. Equivalently `z_old=z+1>1`.
This is the corrected endpoint of the transport argument.

All six Q50 guarded coordinates J,F,alpha,z,eta,zeta are now positive.
Every positive integer is represented by Pos, by the three-square theorem
applied to 4n-3. Choose representations for the four deleted guards
J,F,alpha,z, retaining eta/zeta's existing representations and all
arithmetic coordinates, including the same z. Every Q50 residual then
vanishes. Thus every integer zero of Q45 supplies an integer zero of Q50.
The source's compiler/calibration theorem now applies with all its guards
established.

## Completeness and the shift on canonical witnesses

Assume a finite ZFC refutation exists and take the authentic canonical
Q50 witnesses supplied by its compiler theorem with the complete package-34
tuple. They have `q=2^t` with t positive and odd, F,alpha,C>0,
eta,zeta>0, odd s and i, and square w. The source's canonical shift is
already part of Q50:

    z = z_old-1.

To check strict positivity if starting with an older unshifted witness,
use canonical `X=2^R` and the same growth bound w>q>F. Equation (Told)
says

    (z_old-1)(q-1)=(K0+w)C-F>0.

Hence z_old>=2 and z=z_old-1>=1. This is precisely the argument already
recorded in `DOMAIN_REDUCTION_PROOF.md`, the final paragraph of its
completeness section. Starting with Q50 itself requires no further shift.

Keep its arithmetic coordinates, set `q_half_root=2^((t-1)/2)`, and
choose Pos representations of the positive products F alpha and F C.
Retain the eta/zeta guard parameters. All 28 literal Q45 residuals vanish.

The Q45/Q50 result is an equivalence of **existence** for the authentic
tuple. It is not a claim that every Q50 zero projects to Q45: the dyadic
half-square guard is obtained on the canonical accepting witnesses.
In contrast, the subsequent Q45-to-Q37 and Q45-to-Q34 eliminations are
the separately proved exact integer zero-set bijections.

## Source boundary

This note corrects a coordinate name in the inherited prose and spells out
the deferred guard argument. It changes no preserved upstream bytes,
polynomial, coefficient, variable count, or degree certificate. It does
not claim a new kernel proof of the inherited Pell/compiler theorems.
The exact source files and their snapshot hashes are identified in
`coefficients_source/TRANSFER_LEDGER.json`; Q45 itself is bound in
`coefficients_source/ACTIVE_BINDING.json`.

Primary repository snapshot: `beb0192cb8dc36f78c369c080f2adfbc1887a486`.
Source directory:
<https://github.com/VladimirReshetnikov/ProveIt/tree/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms>.
