# Compatible sign orientation and calibrated cones

## Completed equations and scope

This component supplies seven literal sum-of-squares equations over unrestricted integers:

| Packet | Unknowns | Residuals | Exact degree |
|---|---:|---:|---:|
| quartic37_direct | 37 | 24 | 4 |
| quartic37 | 37 | 24 | 4 |
| sextic30 | 30 | 17 | 6 |
| octic26 | 26 | 13 | 8 |
| degree10_25 | 25 | 12 | 10 |
| degree12_24 | 24 | 12 | 12 |
| degree16_23 | 23 | 11 | 16 |

A packet means the ordinary polynomial obtained by summing the squares of its displayed integer polynomial residuals. Every abbreviation is polynomial; none is an existential variable unless it appears in the ordered variable list. The six fixed coefficient ports are the materialized whole source-34 tuple beta,K0,MC,MF, together with A=2^1113 and B=2^666104. MF is already shifted. BINDING.json and the gzip payloads specify every actual integer. All six constants are positive, beta=2^1064921-1, and beta is 1 modulo 3.

For each packet, ordinary mathematics formalizable in ZFC proves that existence of an integer zero is equivalent to existence of a finite syntactic ZFC refutation. Negation gives the requested consistency equivalence. The inherited native/compiler and Pell calibration remains a mathematical dependency; no new Lean/Rocq certificate or encoded ZFC derivation is asserted. The reductions here are compositional improvements over the reviewed finite catalogue, not claims of a global optimum or a historically new general positivity theorem.

## 1. Two compatible existence reductions

The pinned source71 quartic38 is retained byte-exact. Its 25 rows comprise the usual source64 arithmetic, the square condition X=2u^2, and two positive-value rows. Put

q=beta*J+1, C=q-F-alpha,
T=A*F*B*C-(q-A*F-B*C)^2,
Pos(p,q,r)=1+p^2+q^2+r(r+1).

The guards say T=Pos(cone1,cone2,cone3) and eta*zeta=Pos(e1,e2,e3). Every Pos value is positive; every positive integer has a Pos representation by the three-square theorem applied to 4n-3.

The determinant guard implies F,alpha,C have a common nonzero sign, with the same sign as q. Indeed T>0 implies U=AF and V=BC have one nonzero sign and |q-U-V|<sqrt(UV)<=(|U|+|V|)/2. Hence q has that sign and |q|>(|U|+|V|)/2>=|F|+|C|; alpha=q-F-C has the same sign. Consequently the two older guards F*alpha>0 and F*C>0 may be restored using fresh Pos triples.

For completeness, source71 proves that every permitted canonical accepting witness satisfies q/2<=AF<4q/5 and q/2<=BC<3q/5. These bounds survive the rank-tuning dummy changes. Thus T>3q^2/25>0, so a cone triple exists. The complete source proof and its source-34 support/carry evidence are retained. This step is not a coordinatewise equivalence on arbitrary source zeros: it selects canonical accepting witnesses.

Source70's signed orientation theorem works with those older common-sign guards and eta*zeta>0, and does not assume X positive during rank recovery. It proves that after deleting X=2u^2 and imposing X=2 modulo 3, the other arithmetic recovers X=epsilon*2^R with R odd; the residue forces epsilon=+1. Its hypotheses include X=qW, |W|>=4, an odd nonzero Y/q^3, and the exact source coefficient bounds. They are all preserved here after the old positivity triples are restored. In particular no circular appeal to the original positive-X theorem is needed.

For the direct quartic replace X by 3X3-1, delete X-2u^2, and delete u. At a zero, X is nonzero; X=4q*w_scale and q is nonzero imply |4w_scale|>=4. Thus source70's direct proof applies, and u=2^((R-1)/2) restores the missing square row. There are 37 unknowns and 24 quadratic rows.

For the projection-friendly quartic instead put J_old=3J3+1 and w_scale_old=3w3+1 and delete the same square row and u. Then q=beta(3J3+1)+1 is 2 modulo 3, W=4(3w3+1) is 1 modulo 3, so X=qW is 2 modulo 3 and |W|>=4. The same soundness proof applies.

There is no hidden incompatibility between the two canonical restrictions. Source70 canonical witnesses have q=2^t with t odd, R odd (in fact 3 modulo 4), J_old=(2^t-1)/(2^1064921-1), and w_scale_old=2^(R-t-2), with R-t-2 nonnegative even. Hence J_old=w_scale_old=1 modulo 3. Source71's determinant estimate holds uniformly for these canonical witnesses, including their parity/rank tuning. Select their cone triple, take J3=(J_old-1)/3,w3=(w_scale_old-1)/3, and forget u. This proves completeness of the affine quartic. The direct quartic similarly uses X3=(2^R+1)/3.

Thus both quartics have the required existence equivalence. Their tau^4 coefficient is 1, independently of the fixed ports.

## 2. Thirty integers at degree six

Start from the affine quartic. Write q=beta(3J3+1)+1, W=4(3w3+1), k=eta+zeta and H=4a+3. Make the invertible root translations

tau_old=tau+E(c-eta), D_old=D+ac.

Delete the seven monic coordinates

P=k+E(c-eta), X=Wq, N=q(L+1), C2=c^2,
Delta=a^2+4a+3, V=fo-c, Baux=I^2.

Retain F2 and its equation F2=f^2. The restored old difference row V^2+g-y^2 can be replaced by

F2*o^2-2foc+c^2+g-y^2,

because the replacement minus the restored row is o^2(F2-f^2). This is an elementary reversible row operation modulo a retained equation, not an integrality relaxation. The two root identities are

(tau+E(c-eta))^2-(k+E(c-eta))*E(c-eta)-1
 = tau^2+(2tau-k)*E(c-eta)-1,

(D+ac)^2-(a^2+4a+3)c^2-1
 = D^2+2acD-(4a+3)c^2-1.

After substitution and this row correction every residual has degree at most three. The two cone/sign rows remain quadratic. The defining rows restore all seven coordinates uniquely; the root translations restore both roots uniquely; the retained F2 row makes the row correction reversible. This proves a polynomial bijection of integer zero sets with the affine quartic. The counts are 37-7=30 and 24-7=17. Only the auxiliary norm contains both I and g, and contributes coefficient 1 to I^4*g^2 in the final sum of squares, proving exact degree six.

This combines the source72 ideal-preserving lifting-register choice with source70 orientation and source71 calibrated cone. Neither source alone gives this count.

## 3. Twenty-six integers at degree eight

Again start from the affine quartic, without the preceding root translations. Set k0=1-V+jc+hE. Delete the eleven monic coordinates by

L=q^2-1, N=q^3, X=Wq, C2=c^2, F2=f^2,
g=y^2-V^2, Baux=I^2,
D=Wq+ac+gamma(4a+3), Delta=a^2+4a+3,
zeta=k0-eta, P=k0+E(c-eta).

Their defining rows vanish identically. Every other row has degree at most four. These polynomial assignments and forgetting the assigned coordinates are inverse on integer zero sets. Thus there are 26 variables and 13 rows. The coefficient of a^4*f^4 is 1, from the ordinary strong norm alone, so the final degree is exactly eight.

## 4. A transport pivot at degree ten

In the octic replace alpha by the complement coordinate C, so alpha=q-F-C. This is an invertible affine-polynomial coordinate change. The retained transport equation is

(K0+W)C-F-z(q-1)=0.

It is monic in F. Delete it and F, substituting

F=(K0+W)C-z(q-1), alpha=q-F-C.

Both assignments are integer polynomials. The other arithmetic rows are unchanged except for exact substitution. In particular the packing polynomial can be written

R=(q-F)(q^3-q)-C(q^2-1)+(MC+q MF)(3J3+1).

Its degree is at most five; the determinant guard now has degree at most four. No remaining row exceeds degree five. The resulting 25-variable equation has 12 rows. Its coefficient at w3^2*C^2*J3^6 is 104976*beta^6>0, so its exact degree is ten. The deleted transport row restores F uniquely. This is a zero-set bijection, with no new positivity theorem or calibration change.

## 5. Joint positivity and the 24- and 23-integer companions

For arbitrary integers x,y put

G(x,y,t)=xy-(t^2-x-y+1)^2.

Then x>0 and y>0 if and only if there exists an integer t with G(x,y,t)>0. Soundness: G>0 gives xy>0; if both are negative, the squared term is at least (|x|+|y|+1)^2>xy, impossible. Completeness: for positive x,y set n=x+y-1, so 1<=n<=xy. Choose the nearest integer square t^2 to n. If m=floor(sqrt(n)), elementary rounding gives |t^2-n|<=m, and if n is not a square its square error is <n; if it is a square the error is zero. Thus G>0.

In the octic let x=T and y=eta*(k0-eta). The two old guard triples occupy six private variables. Replace both guard rows by

G(T,eta*(k0-eta),t)=Pos(p,qpos,rpos).

This deletes six private variables and inserts four. Each zero of the new row has both original arguments positive, so independent Pos representations restore the old triples. Conversely the nearest-square lemma and Pos representation give the four new witnesses. This is existential equivalence, not a zero-set bijection on private witnesses.

T is quadratic and eta*(k0-eta) is cubic. The new residual has degree six; its square has coefficient 1 at eta^4*j^4*c^4. Thus degree12_24 has 24 integer unknowns, 12 rows, and exact degree twelve.

Apply the transport pivot of Section 4 to this 24-variable system. T becomes quartic, while eta*(k0-eta) stays cubic. The joint guard becomes degree eight, and no other residual exceeds degree five. One variable and one row disappear, giving degree16_23 with 23 unknowns and 11 rows. Its coefficient at w3^8*C^8 is 429981696*A^8>0. This follows from the leading term -144*A^2*w3^2*C^2 in T, followed by the two squarings in G and the outer sum of squares. Hence the degree is exactly sixteen on the actual fixed tuple, not merely at generic symbolic constants.

## 6. Evidence and comparison boundaries

build.py is newly authored. It reads upstream JSON only as inert data through a restricted AST parser and performs exact symbolic polynomial transformations. It never imports or executes an upstream generator. It checks the literal determinant guard, deleted square row, restoration identities, the seven- and eleven-row eliminations, all variable liveness, degrees and explicit leading coefficients. check.py independently evaluates the literal packet residuals against compact specifications on signed modular assignments, checks all fixed payload hashes and arithmetic identities, and exercises both directions of the nearest-square lemma in finite boxes. These checks establish transcription and finite arithmetic facts, not the unbounded compiler theorem.

The reviewed incoming fixed-degree integer points were38/4,32/6,27/8. The completed outputs37/4,30/6,26/8 improve those counts. The higher-degree points25/10,24/12,23/16 are separate tradeoffs; no assertion of a global Pareto frontier is made. The incoming dossier's25/12 combination was an unproved construction note, not a completed prior consistency equation. All inherited notices and source hashes are retained.
