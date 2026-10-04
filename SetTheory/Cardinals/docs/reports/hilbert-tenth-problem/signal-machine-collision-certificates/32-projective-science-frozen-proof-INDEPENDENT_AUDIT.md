# Independent audit: projective scale shears and the 44-event example

4 October 2026. This audit independently checks the proposed new primitives against the conventional proofs in `../five-signal-planar-realization60-20261004/PROOF.md` and `../fixed-word-invertibility61-20261004/PROOF.md`. It is direct symbolic mathematics: no author/upstream executable, saved schedule, physical trajectory simulator, or other mathematical program was executed.

## 1. Outer-marker primitive: all eight contacts

Assume fixed rational v>0 and 0<x<y<D. Start the messenger at L=0 with velocity +1. At D, launch D with velocity h=(v−1)/(v+1), reverse the messenger, bounce it at Y, restore D on the next outward meeting and reverse, then cross Y,X and bounce at L. Put

    D*=vD+(1−v)y=y+v(D−y),
    t*=(v+2)D−(v+1)y.

The eight event times are

    x, y, D, 2D−y, t*, t*+D*−y, t*+D*−x, t*+D*.

The contacts are respectively X,Y,D,Y,D,Y,X,L. The flight durations are

    x, y−x, D−y, D−y, v(D−y), v(D−y), y−x, x.

These are strictly positive. The moving outer marker is monotone between D and D*, both strictly beyond y. Its speed is strictly between −1 and +1; therefore no target/spectator collision or extra messenger/target meeting occurs. All stationary spectator crossings are explicitly included. The exact chamber on the prescribed initial section is just 0<x<y<D. Its duration is

    T_outer=2[(1+v)D−vy].

This includes v=1: the temporary marker label then has velocity zero, but it still meets a messenger of distinct velocity. The eight-event word is retained.

## 2. Inner-marker scales and their exact additional guard

Put s=(v+2)/3. Scale X and Y about L by s, leaving the restored D* fixed. If s<1 use X then Y; if s>1 use Y then X. For s=1 either order works if both identity scale words are retained.

The X scale has four events. The Y scale has eight, including all four crossings of its stationary inner spectator. Their combined duration is 2(1+s)(x+y). Endpoint ordering in the chosen order leaves precisely the additional condition

    sy<D*, equivalently 3vD+(1−4v)y>0.

For v≤1 this row follows from the initial strict ordering; for v>1 it is essential. In the latter case Y moves outward first, and failure forces its contact with the fixed outer marker no later than its prospective endpoint. Equality gives a simultaneous contact. Thus the row is necessary, not merely a sufficient safety bound.

The full raw word has 20 events, three temporary marker labels, and four supplied guard rows:

    x>0, y−x>0, D−y>0, 3vD+(1−4v)y>0.

At the standard center x=D/3,y=2D/3, D*=sD and D*−sy=sD/3>0. Every internal endpoint is strictly ordered. The chamber is therefore center-strict for every v>0, not only parameters near one. On D=1 it is bounded because it lies in the initial ordered triangle.

## 3. Matrix, compensation, and arbitrary rows

Use ξ=x−D/3 and η=y−2D/3. Direct substitution gives

    N_v = [[s,0,1−v], [0,s,(v−1)/3], [0,0,v]].

Let A_v be its lower-right 2 by 2 block and put

    C_v=s A_v^−1=[[1,(1−v)/(3v)],[0,s/v]].

Its determinant is s/v>0, so the existing positive planar compiler applies. Chronologically perform the raw word, the compiler for C_v at fixed D*, then global scale 1/s. The resulting return is exactly

    (D,ξ,η) -> (D+kη,ξ,η),
    k=3(1−v)/(v+2).

The direct parameter range is −3<k<3/2, with rational inverse v=(3−2k)/(k+3). Arbitrary rational k follows by finite additive subdivision into this interval. Each corrected factor fixes the central ray, so every pulled-back guard remains strictly positive there; subdivision introduces no empty-chamber obstruction. The corrected event count is

    20 + m(C_v) + 24·1[s≠1],

when the two raw identity scales are retained at s=1. Its temporary-marker-label count is 3+t(C_v)+3·1[s≠1].

There is an alternative with one fixed nonzero coefficient and no coefficient subdivision. For a nonzero row r=(a,b), set

    B=[[b,−a],[a,b]], det B=a²+b²>0.

Chronologically run diag(1,B), the coefficient-one shear, and diag(1,B^−1). The result is (D,w)->(D+r w,w). All factors fix the centered ray and have center-strict exact chambers, so their finite pullback intersection is center-strict. The zero row can use any retained positive-duration identity realization.

For coefficient one, v=1/4,s=3/4 and C_v=[[1,1],[0,3]]. Applying the preceding compiler literally gives SL₂ chronological blocks y(−2),x(1/3),y(6), with K=34,T=4, followed by H=8 centered dilation steps. Thus m(C_v)=736. The corrected coefficient-one shear has 780 events, 166 temporary marker labels, 216 supplied guard rows and 950 meta-signals under fresh-messenger-phase labeling. These are nonminimal bookkeeping counts.

The raw determinant is vs²; compensation and global scaling give determinant one. All these words have even length, in agreement with collision parity.

## 4. Independent check of the 44-event example

Fix rational v>1. Follow the 20-event raw word with the 24-event global homothety of factor 1/v. Put r=(v+2)/(3v), so 1/3<r<1. The exact homogeneous return in (D,x,y) is

    (D,x,y) -> (D−((v−1)/v)y, rx, ry).

The suffix adds no guard beyond the raw chamber. Its duration, including all spectator crossings, is

    T=2[(1+v)D−vy]+2(1+s)(x+y)
      +2(1+1/v)[s(x+y)+vD+(1−v)y].

Define c=D−3y/2. It is invariant, and algebraic iteration gives

    x_n=r^n x, y_n=r^n y, D_n=c+3yr^n/2.

The added raw guard at macro n is equivalently

    D_(n+1)−y_(n+1)=c+yr^(n+1)/2>0.

Starting in 0<x<y<D, the complete infinite word is therefore valid exactly when c≥0. If c<0 the displayed expression eventually becomes negative, so a finite first failure occurs. If c≥0 all initial-order and added guards at every macro are strict. On D=1 this infinite-valid set is exactly 0<x<y≤2/3.

For c=0, every position at successive sections scales by r. Since T is homogeneous linear, T_n=r^n T_0 and the total elapsed time is T_0/(1−r): these runs are Zeno. For c>0, the outer phase alone satisfies T_outer,n>2D_n≥2c, so the total time diverges. Thus the same fixed 44-event word has both Zeno and non-Zeno infinitely valid inputs. Its return determinant is r²>0, again consistent with even parity.

## 5. Scope and limitations

The audit establishes the new endpoint chamber, complete primitive chronology, compensation identities, center-strict composition argument, counts under the stated compiler, and the 44-event example. It relies on the preceding compiler's proved exact guard lists and finite deterministic labeling construction; it does not independently re-prove every prior compiler block. Fresh disjoint phase labels remain necessary when concatenating blocks. All counts assume the explicitly retained identity words and make no optimality claim.

The general-row argument realizes projective scale shears fixing the standard central ray. By itself it does not prove realization of every invertible 3 by 3 matrix or classify every projective infinite-validity set. It proves existence on an exact nonempty center-strict chamber, not arbitrary prescription of that chamber. No continuation through a Zeno accumulation is asserted.
