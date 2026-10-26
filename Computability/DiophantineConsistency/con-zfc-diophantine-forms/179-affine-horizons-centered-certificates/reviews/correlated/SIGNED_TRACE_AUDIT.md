# Independent audit: signed unsquared trace and even strong scale

## Result so far

The new normalized kernel with I=4(2r+1)c^2 and V=f(cT-R)-c passes the signed strong-index/parity argument, subject to retaining the source153 carrier/guard bootstrap hypotheses verbatim. Its soundness reduction to the old source requires fresh old strong and auxiliary witnesses, not the unchanged old-source map. That restoration is proved below. The exact endpoint norm, formula binding and final cost/degree have now independently passed; see round22/roots/review/INDEPENDENT_TRACE_REVIEW.md.

## Retained interface, not re-proved calibration

The retained signed bootstrap, using the carrier, guard, normalized strong row and the unchanged residue V=-c (mod |f|), establishes: c0=|c|=psi_B(p)>2; a positive first index n0<p; c0>2p and c0>2R; B=|a+2|>=2; and the retained main/first Pell classification and projection interfaces. The normalized-rank argument in source 06_PROOF.md Section 2 applies to any nonzero I with c0^2|I: for |f|=chi_B(m), |I|=psi_B(m), it gives m=pv with c0|v, hence c0|m and m>2p. These statements do not require an odd scale quotient. In detail, before normalized rank is invoked, odd auxiliary-index classification and folding modulo |f| use |I|>=c0 and |f|>2|I| to recover c0=psi_B(p); the even replacement scale only strengthens the required size inequality. The old source proof's sentence claiming the two literal residues unchanged must be replaced for the new V, as follows.

## Signed soundness of the modified trace

The recurrence gives psi_B(n)=n (mod 2) for every integral B. Since I is even, m is even. If c0 is even, then c0|v forces v even. If c0 is odd, then p is odd by c0=psi_B(p), and m=pv even again forces v even.

Put D=chi_B(p). The composition formula gives |f|=chi_D(v). Since D^2-1=(B^2-1)c0^2, the binomial formula yields chi_D(v)=D^v (mod c0). Since v is even and D^2=1 (mod c0), we obtain |f|=1 (mod c0), and therefore f=+/-1 (mod c0), with either actual sign permitted.

For the literal V=f(cT-R)-c we now have

    V=-c (mod |f|),     V=+/-R (mod c0).

These are sufficient for the retained signed auxiliary-index recovery. Put S=Delta|I|>=2; the auxiliary equation is S^2 V^2-(S^2-1)t^2=1. Classification gives an odd index ell, and the quotient identity modulo |f| yields psi_B(ell)=+/-c0 (mod |f|). Squaring gives chi_B(2ell)=chi_B(2p) (mod chi_B(m)). The retained signed abscissa step-down gives ell=+/-p (mod m). Independently the quotient identity modulo c0, with c0|S and V=+/-R, gives ell=+/-R (mod c0). Because c0|m, it follows p=+/-R (mod c0). The strict inequalities 0<p,R<c0/2 force p=R. No choice of the signs of f,V,t has been discarded.

All later source153 ratio, first-index, projection and centered-strip steps use this rank conclusion and the unchanged carrier/guard data. They therefore establish R odd, X=2^R, c,k,Y>0, A=a+2 positive even, and c=psi_A(R). The compiler is not invoked before these conclusions.

## Exact source closure: fresh old witnesses are necessary

The modified I is even, while source153 requires an odd multiple of c^2. Also its auxiliary expression uses f_old^2, not f_old. Therefore keeping the modified strong pair and T is not a valid source map.

After the preceding conclusions, c and R are odd. Put

    m0=R c, f0=chi_A(m0), I0=psi_A(m0).

Writing D=chi_A(R), composition gives I0=c psi_D(c). Since D^2-1=Delta c^2, binomial expansion gives psi_D(c)=c D^(c-1)=0 (mod c). Thus c^2|I0. Since m0 is odd, I0 is odd; hence I0/c^2 is odd. Define r_old=(I0/c^2-1)/2.

Let S0=Delta I0 and write R=2v+1. Define

    Vstar=chi_S0(R)/S0=Q_v(S0^2),
    epsilon=(-1)^(v+1), V_old=epsilon Vstar,
    t_old=psi_S0(R).

The quotient identities give Vstar=(-1)^v c (mod f0^2) and Vstar=(-1)^v R (mod c). Consequently V_old=-c (mod f0^2) and V_old=-R (mod c). Since gcd(c,f0)=1 and f0^2=1 (mod c), the integer

    T_old=(V_old+c+R f0^2)/(c f0^2)

satisfies V_old=f0^2(cT_old-R)-c. Put y_old=t_old-V_old. The strong and auxiliary source153 rows vanish with r_old,f0,T_old,y_old. Keep all other coordinates, including the carrier and guard witnesses. This is a literal old-source zero. It works for every odd R; no unproved R=3 (mod 4) premise is needed. T_old may be negative, which the unrestricted source allows.

## Canonical completeness of the even scale

Take the same authentic canonical outer family used by source153; it has R=3 (mod 4), A=2 (mod 4), and c odd. With the same m0=R c, f0,I0 as above, both m0 and I0/c^2 are odd. For an even Pell parameter A=2 (mod 4), chi_A(n)=2 (mod 4) for odd n, by its two-step recurrence. Therefore f0/2 is odd.

Double the seed unit:

    f=2f0^2-1, I=2f0 I0.

Then f^2-Delta I^2=1 and

    I/(4c^2)=(f0/2)(I0/c^2)

is odd. Thus r=(I/(4c^2)-1)/2 is an integer with I=4(2r+1)c^2. Also f=1 (mod c). The standard positive odd quotient Vstar=chi_(Delta I)(R)/(Delta I) has Vstar=-c (mod f^2) and Vstar=-R (mod c), since R=3 (mod 4). Therefore

    T=(Vstar+c+f R)/(f c)

is an integer (and positive), satisfies Vstar=f(cT-R)-c, and gives an auxiliary solution. All outer carrier/guard/native data remain unchanged. Thus no incompatible canonical families are spliced together.

## The two distinct source fronts

The degree85 endpoint uses source153's k=R+1+hXY^2 and Budget6. The degree87 endpoint instead uses k=R+1+hXY and Budget8 from the pinned primitive_odd_carriers.md Section1 and roots_baseline/source/FREE_SCALE15_PROOF.md. The latter gives |Y|>|q|^3 and the E=XY first-index modulus; the former gives |Y|>|q|^2 and the ell=XY^2 modulus. The strong/parity/fresh-witness argument above applies to either interface without mixing their hypotheses. Each endpoint restores its corresponding old source; it is not asserted that an arbitrary degree87 zero can be turned into a source153 zero by dividing h by Y.

## Boundary cases

At an actual modified-kernel zero, the guard gives c!=0. Consequently I=4(2r+1)c^2 is nonzero, Delta>=3, and S=Delta|I|>=2. These facts are derived before the rank/classification steps. Negative input coordinates and f<0 are handled above. Positivity of the canonical completeness family is a witness choice, not a soundness hypothesis. This audit does not certify the inherited native compiler or refutation calibration anew.
