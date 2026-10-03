# Independent review of the free-coefficient native index alias

**PASS, with no requested author change.** The [author note](free_coefficient83_native_alias.md) correctly constructs a first/main/index/strong/auxiliary **subsystem** with main Pell index p different from the abstract target R, subject to its stated CRT condition. Its modulo-17 argument also excludes this family from the declared four-bit packing interface for every compatible q. Neither result is a full positive zero of the 83 polynomial or an ordinary-input language conclusion.

The [independent helper](review_free_coefficient83_native_alias.py) and [receipt](review_free_coefficient83_native_alias.json) authenticate the frozen author trio, the 83 source trio, the scaled-family proof/data, compiler-mask proof and half-index proof. They execute none of those Python files. This review reads the complete author note/helper and the inherited [scaled obstruction](first_index_scaled_obstruction.md), and checks the actual native and packing expressions in [83](complete83_free_coefficient_scout.md) as saved JSON.

## The scaled family and positive first-index quotient

For odd t>=11, define

    p=t(t+2), n=t(t+1), X=2^p, Y=2^(t+1),
    E=XY, a=Y(X+1), A=a+2, Delta=A²-1,
    P=2XY²+1,
    (D,c)=(chi_A(p),psi_A(p)),
    (tau,k)=(chi_P(n),2psi_P(n)).

The earlier proof supplies exact first/main norms, kY<c<k(Y+1), and the positive integer gamma=(D-ac-X)/(4a+3)>1. Its strict ratio estimate is sound: the exact balance of the dominant powers, together with the elementary bounds on psi, gives the lower inequality; 2(p-1)(Y+1)<X gives the strict upper inequality. Its recurrence proof of gamma integrality and size uses no first-index equation. Thus eta=c-kY, zeta=k(Y+1)-c, rho=1 and sigma=gamma-1 are positive and restore the actual main-root producer.

The new choice is R=2n-1. Since P=1 modulo E, the psi recurrence gives psi_P(n)=n modulo E. Hence

    h=(k-R-1)/E=(2psi_P(n)-2n)/E

is an integer. It is positive because P>1 and n>1 imply psi_P(n)>n. This proves the actual retained index factor k-hE-R=1. At the same time R-p=t²-1>0. The old first-index congruence is satisfied; the desired main index identification p=R is not.

At q=16, X=wq and Y=sq³ have positive integer w=2^(p-4), s=2^(t-11). For another q=16^ell they hold only when the corresponding exponents are nonnegative, exactly as stated by the author. The subsequent packing obstruction covers all ell>=1, so relaxing these upper restrictions does not weaken it.

## Conditional auxiliary extension is valid

Here p=3 modulo 4. Set f=D and S=Delta*c, so Delta*f²-S²=Delta. Since c is odd, the two conditions

    v=R (mod c), v=p (mod 4p)

are compatible precisely when gcd(c,p) divides R-p. This is a real restriction. The identity

    gcd(p,R-p)=gcd(t(t+2),t²-1)=gcd(t+2,3)

is correct: t is coprime to t²-1, and t²-1=(t+2)(t-2)+3. Thus the simplified divisibility condition in the author note is equivalent, not merely necessary.

For a positive compatible v, v=3 modulo 4. Define V=chi_S(v)/S and y=psi_S(v). The odd-index polynomial identity in the pinned half-parameter proof ensures V is a positive integer. Its zero-argument reduction gives V=-v=-R modulo c. The Pell pair at 2p is (-1,0) modulo f=D, and the pair at 4p is (1,0). Consequently psi_A(v)=psi_A(p)=c modulo f. Together with S²=Delta*(f²-1) and the negative odd-quotient sign, this gives V=-c modulo f.

The main norm gives gcd(c,f)=1 and f²=1 modulo c. Therefore

    T=(V+c+R*f²)/(c*f)

is a positive integer, and V=c*(Tf-1)-R*f² is exactly the source's Bezout argument. Pell's equation at parameter S makes S²*V²-(S²-1)y²=1. Thus all five claimed factor values hold with p different from R. The original inverse would require i=S/(Delta*c²)=1/c, so the old integral strong-rank hypothesis remains unavailable.

The divisions here construct supplied existential witnesses; no operation count or uncharged circuit implementation is asserted. In particular R is an abstract cut value for this subsystem. The independent literal check confirms that the complete source instead computes `r_lhs`; it is not a supplied free port. No input factor or transport factor has been satisfied by this argument.

## The all-q four-bit obstruction

Use precisely the stated weaker mask interface, with native MF0 and paid source coefficient MF=MF0+15:

    0<MC,MF0<15,
    MC=2 (mod4), MF0=4 (mod8),
    popcount(MC)+popcount(MF0)=4.

Independent enumeration gives exactly (6,12), (10,12), (14,4). These necessary arithmetic conditions are not asserted sufficient for an admissible complete compiler recipe.

If the scaled family satisfied the actual source at B=16, then q=15J+1 with J>0 and q divides X=2^p. Thus q is a power of 2, and its congruence modulo 15 forces q=16^ell for ell>=1 because 2 has exact order 4 modulo 15. This deduction does not presuppose a decoded history or an unproved soundness theorem for the free-coefficient candidate.

Modulo 17, q=(-1)^ell and q²-1=0. Since 15 is invertible modulo 17, J=(q-1)/15 is 0 for even ell and 1 for odd ell. The entire packing expression

    R=(q²-Z-qF)(q²-1)+(MC+q*(MF0+15))*J

therefore reduces to R=0 for even ell and R=MC-MF0+2 for odd ell, independently of F and Z. For the three masks the odd residues of R are 13,0,12. The resulting residues of 2R+3 are 12,3,10; the even case also gives 3. All are nonsquares modulo 17. But the chosen family has the exact identity

    2R+3=(2t+1)².

This is a uniform contradiction for every ell, not an extrapolation from a finite search. It rules out this family at the declared B=16 mask interface even before input and transport are considered. It says nothing about other bases or other native families.

## Independent executable evidence and limits

The checker authenticates the actual scale, first/main, index, auxiliary/strong and packing instruction cones. It uses sequential second-order chi/psi recurrences, independently of the author's binary Pell powering. For t=11 it reconstructs and compares **all 23 saved exact fields**, including both positive ratio slacks, gamma's split, positive integral h, both norms, the actual scales, large-rank margins and a CRT auxiliary index found by a short exhaustive residue search. The independently computed c has 22,153 bits and h has 21,986 bits. All saved field bytes and bit lengths agree.

It recomputes every one of the author's 20 declared modular cases and checks a separate bounded list of all 47 odd t from 11 through 103. This list is a finite supplement, not a classification of compatible t. In particular the failed cases remain failed; no claim of automatic CRT compatibility is introduced. For the exact t=11 case, the half-index and full-period congruences are checked on actual integers. The enormous V,y,T are not materialized: their existence follows from the reviewed recurrence/CRT argument above.

The mask check independently constructs the permitted low-bit patterns, lists all quadratic residues modulo 17 and verifies the two symbolic parity classes. An additional 144 full integer packing evaluations, at 16 different q powers and three F,Z pairs per mask, corroborate the all-q proof. Those evaluations do not substitute for it and are not compiler zeros.

The receipt contains no new polynomial source or operation record. It deliberately records `full_polynomial_zero=false`: first/main/index/strong arithmetic and conditional auxiliary extension leave the input, transport and actual packing constraints unresolved, and the stated packing obstruction excludes this particular family at the four-bit interface.

After installation, replay from any working directory:

    python3 review_free_coefficient83_native_alias.py --root ABS_WIP --expect ABS_RECEIPT

While staging, `--author-root /tmp` and, if needed, `--scout-root /tmp` select the frozen new bytes; all older proof pins resolve under ABS_WIP. `--output PATH` writes a stable receipt independent of those directory choices. Fresh normal and optimized Python exact replays from `/` pass. All checks use explicit exceptions, and receipt comparison is recursively type-exact. No predecessor execution or repository write occurs.
