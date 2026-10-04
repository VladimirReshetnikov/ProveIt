# Independent bounded review: rational reconstruction on the all91 boundary

**PASS within the stated scout scope; no correction requested.** The rational reconstruction demonstrates a real boundary of the fixed-polynomial absorption result. It does not establish a new universal source, operation saving, or sign-free elimination of the strong-root witness.

Reviewed frozen author pins:

| File | SHA-256 |
|---|---|
| `complete84_rational_root_scout.py` | `7d7766f6536be28a3819d1764a4fbb31f70ce91f47a313fd22d57384787cde06` |
| `complete84_rational_root_scout.json` | `ab7e0a11e9cc04b961085a2dae6b94eff43761c155cdae2ace4a4b29a29348c2` |
| `complete84_rational_root_scout.md` | `18d60bed0230423e9093d021934ddafe9c4e40f2d01a13ffe71b85945a82ab0a` |

Read scope: full author note and helper, authenticated receipt metadata/check list/local ledger, all 84 literal parent rows and all 25 parent supplied ports, and the parent's positive-domain transfer statements. Actual parent JSON pin is `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`; its companion pin is `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. The accepted all91 proof is pinned at `1280fb32702c4ec99f69807ee4b6fd0bdbd5f83830e5187c41bfbc81da7935b7`; its full proof was authored/read earlier, and its hash was authenticated here. No frozen or new author helper was executed or imported in this review. This note is an independent mathematical/source-interface challenge, not a separate full coefficient-array replay.

## Independent algebra and binding

The literal source gives `Delta=A`, `c=R10a`, `R=r_lhs`, `T=auxiliary_quotient`, `y=y_aux`, `S=Delta*i*c²`, `Q=S²`,

    V=c*T*f−c−R*f²,
    Na=Q*V²−(Q−1)*y²,
    Ns=Delta*f²−Q,
    F84=P5*Na*Ns−Delta.

The five factors in `P5` are exactly the first, main, input, index and transport factors and are f-independent. The two direct f consumers are exactly the square `L16` and `auxiliary_Tf`. The cut binding does not incorrectly free `c²`, `S` or `Q` from their actual producers.

Write `l=c*T`, `D=1+Delta*i²*c⁴`, `b=c+R*D`, and `E=f²−D`. Then `V=l*f−b−R*E`. Direct expansion independently yields

    Na−1 = A_rat−B_rat*f + E*q_aux,
    q_aux = Q*(l²−2*R*l*f+2*R*b+R²*E),
    A_rat = Q*(l²*D+b²)−(Q−1)*y²−1,
    B_rat = 2*Q*l*b,
    Ns = Delta*(1+E).

Consequently the full-source identity checked by the helper is correct:

    F84−Delta*(P5*(A_rat−B_rat*f+1)−1)
      = P5*Delta*E*(q_aux+Na).

This is an all-ring identity. The simpler equality `A_rat=B_rat*f` requires the actual parent strong and auxiliary unit equations; the note makes that distinction explicitly.

Every numerator/denominator ingredient is on the actual f-independent boundary, including the extra `T,y,y²` values beyond E88. Thus the older rational-E88 absorption argument does not apply to this quotient. The parent positive-zero theorem gives `E=0`, `Na=1` and `R>0`, so `B_rat>0` and the quotient exactly recovers the original positive integer f. Inherited universality supplies an infinite accepting language for a suitable fixed program; retaining all those original zeros refutes an unrestricted rational-function version of the all91 finite-input conclusion. No new compiler construction is needed for that sharpness observation.

## Domain and elimination checks

Denominator nonvanishing is stronger than positivity at original zeros and was checked separately. On the positive supplied-port domain, the actual source makes `Delta,c,i,T` positive integers. Hence `D>c>0`; integral `R` cannot satisfy `c+R*D=0`. Therefore `B_rat` has no poles there, although its sign off the original zero set is not forced positive.

For `K=A_rat²−D*B_rat²`, a nonzero denominator and integral D imply that the rational square root `A_rat/B_rat` is an integer: in a reduced fraction p/q, `p²=D*q²` forces q=1. The positive sign does not follow. In the explicitly local example, f=−3 gives `V=−253`, and `64*253²−63*255²=1`, while `Ns=8`. The example's c=1 cannot be the actual positive source `R10a=ksn2+eta`; it is correctly identified as a component example, not a full native counterexample.

The whole-output elimination condition uses `[P5*(A_rat+1)−1]²−D*(P5*B_rat)²`, distinct from K. Neither squared condition alone proves positive reconstruction or retains all full-source implications. These obligations remain open in the scout. No common-coordinate equivalence for a new complete integer source is claimed.

The explicit local schedule has 17 numerator/denominator producers (10M+7A), then four additional producers (3M+1A) for K. All 21 are charged and reach K; the precomputed boundary, remaining parent source, finalizer and possible positivity enforcement are excluded from this **local** ledger. It cannot be subtracted from 84. The unchanged full84 minimum and separate fixed-polynomial all91 theorem are unaffected.
