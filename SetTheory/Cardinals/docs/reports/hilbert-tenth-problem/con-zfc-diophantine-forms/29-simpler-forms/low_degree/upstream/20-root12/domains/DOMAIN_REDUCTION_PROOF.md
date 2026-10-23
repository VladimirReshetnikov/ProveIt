# 54 unrestricted integers at degree four; 46 at degree eight

## Current complete coefficient instantiation

Every main JSON packet and its builder in this release selects the complete
`T4-4094-binary-copy-zero-padding-5pow11` tuple from
`../coefficients/COEFFICIENTS.json`, with tuple SHA-256
`726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
The aliases are Bm1/beta -> beta, Kconstant/K0 -> K, MC -> MC, and
MF -> MF_source. MF_source is the shifted port MF_native + B - 1.
The whole-tuple transfer proof is `../coefficients/COEFFICIENT_PROOF.md`;
it preserves the native interface, rank congruence, parity, positive odd i,
and positive square w required by the signed and low-degree reductions.
Here B = 2^(5^11). References below to original06/blank67 and d = 5^67
describe the historical source proof, not the numerical instance selected
by this release. Its same completeness argument applies through the
proved transfer with odd d = 5^11 and odd five-power tableau area.
No individual coefficient is mixed with another compiler's tuple.
The vendored source evidence remains unchanged.

## Result and scope

The historical derivation takes the four integers `beta,K0,MC,MF` from the coherent original
blank67 compiler tuple, with `beta=B-1` and `MF` the shifted source port.
At the pinned repository commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, this tuple has the exact finite
recipe in
`14-integer29/vendor/blank67/compiler_constants.py` and the associated
K215 transition data. That recipe and its exact output are also included
locally as `sources/14-integer29/vendor/blank67/compiler_constants.py` and
`ORIGINAL_COEFFICIENTS.json`. No coefficient is a variable and no numeral is
replaced by a different compiler's numeral individually.

The artifacts in this directory define integer polynomials Q54 and P46
such that

    Q54 has a zero in Z^54 <=> P46 has a zero in Z^46
      <=> K215 halts on the blank tape
      <=> there is a finite syntactic ZFC refutation.

Thus the assertion that either polynomial has no integer zero expresses
Con(ZFC), with the same exact syntactic proof predicate as the pinned
machine endpoint. Q54 has exact degree 4 and P46 exact degree 8.
The direct quartic comparison is 60 integer variables to 54, not a claim
of global optimality. The positive quartic remains at 32 variables.

This is an ordinary mathematical reduction relative to the existing
Pell/compiler proofs, not a new Lean/Rocq formalization. The check script
certifies the explicit polynomial identities, counts and degrees. It
cannot certify either consistency or inconsistency of ZFC.

## Explicit construction

Start with the 32-coordinate, 23-quadratic system in package 12, whose
literal expanded residuals are vendored as
`sources/12-gap-norm14/quadratic/quartic32.json`. Its coordinates are

    J,F,alpha,z,f,h,i,s,w,tau,eta,zeta,y,gamma,o,j,
    N,E,P,c,a,X,D,C2,G,L,F2,V,g,I,Baux,Delta.

The abbreviations are

    q=beta*J+1, k=eta+zeta, H=4*a+3, C=q-F-alpha,
    R=k-1-h*E.

The equations, all quadratic after these abbreviations are expanded, are

    L=q^2-1;               N=q*(L+1);          X=w*q;
    a=E+s*N;               E=X*(a-E);          c=k*(a-E)+eta;
    P=E*(c-eta)+k;         tau^2=P*(P-k)+1;
    D=X+a*c+gamma*H;       Delta=a^2+H;        C2=c^2;
    D^2=Delta*C2+1;
    G=(q-1)*(q-F)+alpha;   R=L*G+(MC+q*MF)*J;
    (K0+w)*C=F+z*(q-1);
    F2=f^2;               V=o*f-c;             V=j*c-R;
    g=y^2-V^2;            I=i*C2;              Baux=I^2;
    Baux=Delta*(F2-1);    y^2=Baux*g+1.

For Q54 replace i everywhere by `2*r+1`. Retain the other 31 coordinates,
and add an independent integer u and the quadratic residual `w-u^2`.
For each of exactly the seven symbols

    J,F,alpha,z,s,eta,zeta

add three independent integer parameters `v_pos1,v_pos2,v_pos3` and the
residual

    v-1-v_pos1^2-v_pos2^2-v_pos3*(v_pos3+1).

Q54 is the sum of the squares of these 31 literal residuals. There are
`32+1+7*3=54` independent integer unknowns: r replaces i and is not an
extra unknown. Every residual is quadratic, and tau occurs in only the
first Pell residual, with coefficient +1 on tau^2. Hence Q54's coefficient
of tau^4 is exactly 1. Its degree is exactly four.

For P46 substitute the seven Pos expressions and `w=u^2` directly into
the original 23 residuals, again replacing i by `2*r+1`, before taking
the sum of squares. The resulting count is `32+7*2=46`; r and u simply
replace i and w. Residual degree is at most four, so polynomial degree is
at most eight. The first residual's degree-four component is
`-beta^2*(J_pos1^2+J_pos2^2+J_pos3^2)^2`, which is nonzero for beta>0.
The degree-eight homogeneous component is a sum of squares of the
nonzero degree-four components, so it cannot cancel. Degree is exactly
eight. The expanded symbolic coefficient of `beta^4*J_pos1^8` is 2, from
the first residual and the G residual.

`integer54_quartic.json` and `integer46_octic.json` include the complete
variable lists, expanded residuals, and expanded sparse polynomials.
`build_domains.py` checks that eliminating the guard coordinates and w
from the quartic system gives exactly the octic system, with the eight
added residuals becoming identically zero.

## The positive surjection

Define

    Pos(x,y,z)=1+x^2+y^2+z*(z+1).

It is strictly positive on Z^3 because z(z+1)>=0 for every integer z.
For any n>=1, the integer 4n-3 is 1 modulo 4, so it is not of the forbidden
three-square shape 4^a(8b+7). By Legendre's three-square theorem it is a
sum of three squares. Modulo four exactly one square is odd and the other
two are even. Write them as (2z+1)^2,(2x)^2,(2y)^2; division of the
identity by four gives n=Pos(x,y,z). This is a genuine surjection onto all
strictly positive integers, without rational or divisibility conditions.

## Soundness: exactly seven guarded coordinates suffice

The seven guards force their named coordinates strictly positive;
`i=2r+1` is nonzero and `w=u^2>=0`. All other coordinates initially range
freely over Z. In particular we assume no signs for the auxiliary
quotients o,j, for f,y,tau,gamma,h, or for any of the lift registers.

1. The scale equations force `q>1`, `N=q^3>0`, `Y=a-E=s*q^3>0`,
   `X=wq>=0`, `E=XY`, and `a=Y*(X+1)>0`.
   Consequently `c=kY+eta>0`, `C2=c^2>0`, `H=4a+3>1`, and
   `Delta=(a+2)^2-1>0`.

2. The case u=0 is impossible. It would give X=E=0 and a=Y. The D
   definition then gives D=ac+gamma*H. Since Delta=a^2+H, the main norm
   `D^2-Delta*c^2=1` reduces to `0=1 (mod H)`. Thus w>0 and X>=q.
   This argument precedes every Pell rank or growth argument.

3. Transport has positive right side and positive factor K0+w; hence
   C>0 and F+alpha<q. The inherited packing bounds therefore apply,
   including `3q+1<R<q^4-2`, `E>=q^4>R+2`. The index equation is
   `k=R+1+hE`; it forces h>=0 because k>0. Thus c>2R.

4. Equations 6-8 give the original first norm

       tau^2-X*Y^2*(X*Y^2+1)*k^2=1.

   The first/main Pell bootstrap, using |tau| and |D|, gives
   `c=psi_A(p)`, `p>n>=24`, `c>2p`, and `c>A*Delta^2`, where A=a+2.
   These arguments require no auxiliary T,o,j and do not use their signs.
   They are exactly the preliminary signed-domain steps of package 14,
   and the same bootstrap is recorded in package 12's quartic proof.

5. Equations 16 and 20-22 give

       (i*c^2)^2=Delta*(f^2-1).

   Since i is nonzero, the ordinary strong-rank theorem applies to |f|
   and |i| at the preceding growth bound. It yields
   `|f|=chi_A(m)`, `p|m`, `c|m`, and in particular `c|psi_A(m)`.
   Consequently `f^2=1 (mod c)`. This congruence is obtained only after
   applying rank; it is not obtained by invalid division modulo c.

6. The exposed quotient equations give `o*f+R=(j+1)c`. Hence

       o+R*f = f*(o*f+R)-o*(f^2-1)

   is divisible by c. Define the integer `T=(o+R*f)/c`. There is no sign
   requirement on T. Its substituted auxiliary polynomial is exactly

       c*(T*f-1)-R*f^2 = o*f-c = V.

   The equations for g,Baux,y give precisely

       (i*c^2)^2*V^2-((i*c^2)^2-1)*y^2=1.

   Thus the exposed-quotient solution yields a solution of the ordinary
   signed 15-coordinate system audited in package 14, using the same
   odd i and square w. Its transport quotient is `z_old=z+1>0`, since

       (K0+w)C+(q-F)-(z+1)(q-1)=1.

   Every hypothesis of that signed theorem has now been established.
   The theorem recovers the positive rank R, excludes the negative main
   root, proves X=2^R, decodes the native constraints and yields a finite
   accepting blank computation. No tuplewise positivity restoration for
   f,o,j,T,V or y is asserted or needed.

This establishes soundness for arbitrary integer zeros, not merely
canonical witnesses or a bounded test sample.

## Completeness: compatible odd i and square w

Suppose the blank machine halts. The original blank helical construction
admits sufficiently large spatial width h0 and temporal height Htime
chosen independently to be powers of five. Its literal proof says so at
lines 68 and 90 of the vendored `blank_helical_proof.md`. Therefore
Ncells=h0*Htime is odd. The original fixed exponent d=5^67 is odd, and
`q=2^t` with `t=d*Ncells` is an odd exponent. The canonical actual packed
rank satisfies `R=3 (mod 4)` and `R>t`. Consequently

    w=2^(R-t)=u^2,       u=2^((R-t)/2),

with u a positive integer. This is an existence restriction on canonical
witnesses, not an assertion that every old solution has square w.

Let c=psi_A(R), which is odd. Choose the auxiliary rank `m=cR` rather
than the older rank 2cR. The binomial expansion of
`(chi_A(R)+c*sqrt(Delta))^c` shows `c^2|psi_A(cR)`: the first odd term
contains c*c, and every later odd term contains at least c^3. The quotient
`psi_A(m)/c^2` is odd since m,c are odd. In the ordinary system take

    f=chi_A(m),          i=Delta*psi_A(m)/c^2.

At the canonical power-of-two witnesses a is even, hence Delta is odd;
therefore i is a positive odd integer. Set r=(i-1)/2.

Package 14's odd-multiplier completeness proof constructs V,y and the
positive exposed quotients

    o=(V+c)/f,           j=(V+R)/c.

They satisfy V=of-c=jc-R, all the ordinary strong/auxiliary equations,
and the same canonical tableau and half-binomial witnesses. The lift
registers are assigned their displayed values. No additional sign
condition is imposed on those registers in the unrestricted-integer
artifact.

Finally the canonical transport shift z=z_old-1 is strictly positive.
Indeed w>q>F and C>=1 imply `(K0+w)C-F>0`; the exact old transport
identity says this is `(z_old-1)(q-1)`. Thus z_old>=2. This argument is
also explicit in package 12's quartic proof. Surjectivity of Pos supplies
the 21 free guard parameters. We obtain a Z^54 zero, equivalently a Z^46
zero, as required.

## Dependency and evidence boundary

Pinned sources actually inspected and vendored:

- `12-gap-norm14/proofs/quartic32_proof.md`: literal quartic lift,
  preliminary signed bootstrap, exposed quotient restoration and shift.
- `12-gap-norm14/quadratic/quartic32.json`: literal 23 residuals.
- `14-integer29/proofs/signed_domain_proof.md`: seven guards, odd
  multiplier, square scale, signed rank and negative-root exclusion.
- `14-integer29/dependencies/blank_helical_proof.md`: independent
  five-power padding, canonical actual-rank tuning and positivity.
- `14-integer29/dependencies/fixed_blank_67_proof.md`: baseline compiler,
  fixed coefficients, main bounds and endpoint.

The exact fixed-numeral recipe is referenced by immutable repository
commit; its astronomical values are not expanded in decimal here. A
later coherent compiler tuple may be substituted only after verifying
that its canonical completeness presentation retains odd t and R and
all the same arithmetic interface assumptions. Merely mixing the source
port MF or another numeral from another compiler is not justified.

## Low-degree elimination frontier appendix

The primary additional artifacts are `integer45_degree6.json` and
`integer39_degree8.json`. They improve the release's 52-integer sextic
and 47-integer octic, respectively, while the 54-variable quartic above
improves its 60-integer quartic.

Use the exact two pinned source packets under
`sources/15-release/evidence/diophantine_zfc_round2/quadratic/`:

- `start_only_sextic25.json` has 25 coordinates and 16 residuals of
  degree at most three. It uses the normalized strong multiplier and
  the first-root shear `tau_root=tau_tail+E*(c-eta)`.
- `ordinary_octic20.json` has 20 coordinates and 11 residuals of degree
  at most four. It uses the ordinary strong multiplier and merged
  auxiliary quotient T, here named `auxiliary_quotient`.

The source `integers/SIGNED_DOMAIN_PROOF.md`, Section 7, explicitly
establishes that these register eliminations are polynomial identities
on arbitrary integer tuples. The shear of tau is an affine bijection
of its unrestricted integer coordinate. No extra positivity guard for
tau_tail or an eliminated register is required. We additionally apply
package 14's odd-i, square-w refinement to the restored certificate:
normalised i in the sextic, ordinary i in the octic. Both versions are
proved in package 14. This argument preserves existence in both
 directions and uses the same original blank67 coefficient tuple.

Here `transport_quotient` is the original source quotient, not the
shifted z used in the 32-coordinate quartic. No shift is made in either
new low-degree artifact. It remains strictly positive through Pos.

For either parent, replace i by `2r+1`, retain w and add `w-u^2=0`,
and retain the seven guarded source coordinates while adding their
21 Pos parameters and seven quadratic guard equations. The all-integer
solvability proof is now exactly the package-14 theorem after restoring
the omitted registers. This initially gives 47 coordinates with degree
six from the 25-coordinate parent and 42 with degree eight from the
20-coordinate parent. The following are exact eliminations of redundant
guard coordinates, not relaxations of the positive-domain hypotheses.

For the sextic, alpha occurs linearly in `-L*alpha` and in transport,
and the original transport quotient occurs only in
`-beta*Jrep*transport_quotient`. Substitute their Pos polynomials directly
and delete their two guard equations. All residuals still have degree
at most three. The resulting polynomial is a sum of 22 squared
residuals in 45 unrestricted integer variables. Its expanded coefficient
of `Jrep^2*L^2*s^2` is `beta^2>0`, coming from the square of the
`-beta*Jrep*L*s` term. Thus the degree is exactly six on every authentic
coefficient tuple, not merely on a diagnostic specialization.

For the octic, alpha, the original transport quotient, and zeta may all
receive their Pos expressions directly. Alpha's highest relevant term
is `-beta^2*Jrep^2*alpha`, of degree four after substitution. Transport's
quotient term becomes degree three. The terms involving zeta have
original degree at most three and are linear in zeta, so become degree
at most four. Delete those three guard equations and their three
retained coordinates. The result is a sum of 16 squared residuals in
39 unrestricted integer variables. Its coefficient of `Jrep^6*s^2`
is `beta^6>0`, from the square of `-beta^3*Jrep^3*s`, proving exact degree
eight for every authentic beta>0.

The generator `build_tradeoffs.py` enumerates only the 256 subsets of
the seven guard coordinates and w that can be eliminated by their
explicit quadratic definitions. It checks each polynomial degree and
the exact elimination identities. This is a finite construction check,
not a claim that the resulting count is optimal among Diophantine
representations. For completeness the same finite sweep also emits
37-variable degree-10, 35-variable degree-12 and 34-variable degree-16
variants; these are optional higher-degree tradeoffs, not additional
claims of a lower unrestricted count than the separate 28-variable
construction.

