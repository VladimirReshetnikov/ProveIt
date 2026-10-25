# Combined refined cap source: helper normalization, signed pool, then F

This is a complete ordinary composition at the accepted literal cap source.
It is a code/proof checkpoint only: no new program has been imported, compiled
or executed and no successor source or measurement has been emitted. The
finite checker will bind the specified interface; it does not replace the
unbounded arguments below. Every index here is in the immutable parent body.

The parent source packet is `research/signed-pell-cap-source`, manifest
`53244a0a26bcfe2411c28adf2c6d74f7a4618c0c42c7904e8818be4e3f9a6ef5`.
The three independently reviewed ordinary ingredients are:

- unoriented signed cap/pool, seal
  `9fbb6fc816b0526bc16285c5198a2c7ffa179bdf4e1f9331fc83605d639e8be2`;
- t-only recovery of F, seal
  `e5c75ddaf0a8aebc23ced3b780122a15bbfdf317ea59e2457af32e755e0e0886`;
- four-coordinate helper reflection, seal
  `77d184efa8282e84c68b3252bfd41bb9cecb31c4983fb2d0824dfd8c8d77a493`.

The F ingredient by itself retains the old cap summand. That theorem is not
invoked on the new kernel. Section4 below re-proves its bootstrap with the
signed-A orientation lemma of the unoriented theorem instead. Likewise the
old cap-in-pool A-orientation theorem and all-positive-index ledger are not
used before recovering F.

## 1. Exact simultaneous edits and exposed front

Let the parent cap be C=v387, scale A=v246, frame W=v245 and pool quotient
h=v395. Remove body row217, the direct C-W Legendre graph, and its private
coordinates396,397,398. Replace body row219 by its complete old polynomial
minus (v387-v245)^2. This is exactly

    sum15 (Yi-ki)^2 - (A-1)h = 0.                 (J)

The separate squared-cap graph at row218 remains, with its own triple399..401.
No positive C predicate or cap term remains in (J); h stays signed.

Remove appended old F graph2 at row337 and its triple408..410. Remove appended
helper graphs27/30 at rows361/362 and their triples480..485. All four removed
triples occur only in their own complete graph rows. Replace helper27/30 by one
fresh Legendre graph for v255-4>=0. Preserve every other row, graph, label,
variable metadata and guard-auxiliary name, apart from the exact index change
required by deleting unused private slots and placing fresh auxiliaries.

The unchanged native/front coordinates are0..245 and376..385. The retained
front rows are0..201 and324..334. W is part of that fixed front. All37 actual
frame atoms and all54 base/index/output port occurrences lie in it. Replacing
private Pell witnesses later is permitted; claiming the whole body fixed is
not. All18 unsquared power requests, five shared T definitions and the signed
t+1 recurrence remain literal old rows. There is no compiler or quartic here.

## 2. Normalize the helper FIRST

Write V=v251,d=v252,H=v254,e=v375,U=v250,Bpart=v255,C2=v389.
The complete helper body equations are

    H-A V=0, U^2+V^2-H^2-1=0,
    Bpart-4V(d+1)=0, V-C2(e+1)=0.

Reflect only V,d,H,e by

    V'=-V, d'=-d-2, H'=-H, e'=-e-2.

This involution negates rows205/323 and fixes every other parent body row.
It also fixes the newly modified pool, all retained graphs and the new Bpart
graph: none uses these ports outside the recorded four helper rows. It
preserves the complete noncontiguous native front, F, A, every primary pair,
C, its squared bound and W. Deleting the C-W graph does not affect any of
these reflection identities.

The new graph gives Bpart>=4. Hence row207 gives V(d+1)=Bpart/4>0, so V!=0.
If V<0 apply the reflection; otherwise use the identity. In either case the
normalized zero has V>=1,d>=0. Choose fresh old helper triples for V-1 and d.
This is justified before any cap, index, power, F or A sign interpretation.
The following sections apply to that normalized zero. No helper sign is
assumed directly of an arbitrary unnormalized input tuple.

## 3. Only t, absolute frame bounds and SIGNED targets before F

Retained direct graphs give t0=v0>=0,r=v7>=0,s=v8>=0,o=v185>=0 and
v247>=0. Actual rows3/167 give B=v5=r+s+1>=1 and q=v179=B+o+1>=2.
Thus t=16+t0>=16. Row0 gives rho=v4=F^2>=0 even for signed F.

The unchanged full frame is W=2(2+sum37 atoms^2). Consequently W>=516,
all fifteen requested indices satisfy |ki|<W, and every actual base and
output has absolute value<W. In particular q<W,1+rho<W and |v6|,|v181|<W.
The scale norm is A^2-W^3(W+2)(v247+1)^2=1. The accepted absolute-base frame
argument gives a=|A|>=(W+1)^W and a-1>4W^3. No sign of F,A,y,K or the other
requested indices is a premise. Only the t request is known positive/nonzero.

Use the generic unoriented theorem with all fifteen ki SIGNED. The squared
cap graph implies C^2>=1+sum Yi^2. If |C|=1, all Yi=0 and (J) says that
0<sum ki^2<W^3<|A-1| is divisible by A-1; the strict inequality uses t!=0.
This is impossible. Hence |C|>1, its absolute Pell index i is at least2,
and |C|>=2a>W. The normalized positive V,d, complete comparison norm and
C^2 divisor now meet the unoriented absolute cap-anchor hypotheses. They
give |C|=Y_W(a), with neither sign of C selected.

Each main absolute index ji is<W by the squared cap. Reducing (J) modulo
A-1 bounds only the finite signed index-error representative

    0<=sum (tau_i ji-ki)^2<4W^3<|A-1|.

It is divisible by A-1, hence zero. Therefore Yi=Y_ki(A) and
Xi=+/-X_ki(A), including signed/zero requests. The actual huge sum (J) is
not bounded this way. No sign of A or h has been inferred, and the removed
cap-in-pool orientation argument has not been reused.

## 4. Signed-A q support, SAME-pair base one, then recover F

For positive k and base n>=2 define canonical signed-A values
X=X_k(A),Y=Y_k(A),H=X+(n-A)Y,J=X-(n-A)Y and T=2An-n^2-1.
The polynomial identities HJ=1+T Y^2 and H_(k+1)=nH_k+TY_k imply
H=n^k modulo T for either sign of A. The frame supplies |T|>W^W.
For |m|<W,n,k<W, both |m-n^k| and |m*n^k+1| are<W^W.
The canonical-abscissa branch therefore gives m=n^k. The opposite branch
would give m*n^k=-1, impossible since n^k>=2. Canonical X or Y need not
be positive when A<0.

Apply this lemma FIRST to actual call4, parent row254, with base q>=2,
positive t and output v181 on pair257/258. This orients Xt=X_t(A) and
gives v181=q^t. Then call0, parent row227, uses that SAME canonical pair
at n0=1+rho=F^2+1>=1. The recurrence gives v6=n0^t modulo its T0, even
at n0=1, and |v6-n0^t|<|T0| gives v6=(F^2+1)^t>=1. There is no separate
base-one orientation claim: the real opposite-branch m=-1 endpoint has
already been excluded by the q request on the same pair.

The exact front row combination r1+r2-r3=v6+s-FB gives FB=v6+s>=1.
Since B>=1, integrality forces F>=1. Choose fresh witnesses for the omitted
F Legendre graph. Only NOW can a theorem whose hypotheses include F>=0 be
applied; neither all-target positivity nor its old sign ledger was used to
justify the preceding cap or q/base-one arguments.

## 5. Complete soundness by the accepted unoriented existence theorem

The normalized zero now has F>=0, old V/d graphs restored, the squared cap,
the primary-only pool, all retained native graphs and the full frame. These
are precisely the unoriented theorem's hypotheses, with the lower C-W graph
and cap summand absent as that theorem specifies. Apply its COMPLETE ordinary
existence proof, not the old positive-A joint-pool theorem.

That proof now restores all original positive-index/power/native meanings in
its stated order, and constructs a fresh positive A, scale witnesses, all main
Pell pairs and the derived pair, cap C=Y_W(A)>0, shared T values, power
quotients and common comparison/CRT witnesses. Its new lower and squared cap
triples and full old pool quotient supply a zero of the EXACT original sealed
cap source at the SAME front0..245,376..385. This proves the combined source's
soundness at the inherited native C222/refutation calibration. It is not an
identity of old and new private body tuples or a sign claim about every input.

## 6. Complete converse and witness bookkeeping

Begin with any original sealed cap-source zero. Its accepted theorem gives
A>0 and C=Y_W(A). Forget the lower graph and reset only the old signed h to

    h_new=h_old-(C-W)^2/(A-1).

The quotient is integral because C=W modulo A-1; h occurs nowhere else.
This exactly supplies (J). Forget the old F and two helper graphs. Original
V>=1,d>=0 imply Bpart=4V(d+1)>=4, so choose a fresh Legendre triple for the
new helper graph. All remaining coordinates and witness triples are retained
under the explicit complete index maps. This constructs a combined-source
zero. It does not leave h incorrectly fixed or identify all guard witnesses.

The two directions establish ordinary EXISTENCE equivalence at the fixed
native front. The checker must independently bind every unchanged row and
graph, every deleted private occurrence, the pool subtraction, all reflection
identities/involutions, full frame/port membership, and all18 unsquared/five-T
interfaces. Its pre-F ledger may use only the stated t/r/s/o/Z premises and
the normalized helper signs. The later full ledger is staged AFTER F recovery.
Actual mutation controls are required after both full static reviews. Nothing
in this packet predicts an optimized variable, residual, term or height count.
