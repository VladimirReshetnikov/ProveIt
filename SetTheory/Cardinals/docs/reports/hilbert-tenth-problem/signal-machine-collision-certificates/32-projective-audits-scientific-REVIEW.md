# Fresh independent audit of the fixed-center projective signal compiler

Date: 2026-10-04 UTC  
Verdict: **ACCEPTED, within the stated scope. No mathematical correction required.**

## 1. Source binding, execution boundary, and evidence

This review concerns the frozen directory `projective-signal-shears62-20261004`, specifically `PROOF.md` with SHA-256

`502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47`.

The entire main proof, full `RULES44.json`, full `static_algebra.py`, section/guard and native-gap declarations, and both preserved dependency proofs were inspected as text. The previous in-packet audit was read only after independently reconstructing the principal arguments. Its conclusions were not used as a substitute for checking them.

No author checker, author constructor, prior mathematical program, physical simulator, or saved collision schedule was executed or imported. The only executed mathematics in this audit is the freshly written, displayed, and inspected `independent_static_audit.py`. It uses the installed SymPy 1.14.0 for rational-function identities and matrix algebra, and reads rule declarations strictly as inert JSON. It performs no physical-state advancement, next-event search, or schedule replay. Its literal-rule comparison is a comparison of finite strings and assigned speeds.

The fresh check run passed **157 named algebraic, structural, and authentication checks**. This is supporting evidence for the conventional proof below, not a proof-assistant verification. The count deliberately includes all 44 literal-rule comparisons and all 44 outgoing-phase speed comparisons, so it must not be advertised as 157 independent mathematical theorems.

Evidence:

- `evidence/independent_checks.json`: names, source hashes, counts and result
- `evidence/rule44_static_review.json`: separate record for every explicit rule
- `evidence/frozen_before.json` and `evidence/frozen_after.json`: all 17 source objects, including directories, with modes and nanosecond modification times; every file also has byte length and SHA-256
- The source manifest's 12 listed file hashes and lengths all match

The frozen tree's bytes, file and directory modes, modification times, and object set are unchanged. This audit writes only to its separate new directory. Access times are not claimed invariant.

## 2. What is inherited and what is established here

The new proof uses the following precise earlier interface:

For rational C in GL₂ and rational λ>0, F(C,λ) realizes λ diag(1,C), on a complete exact center-strict rational cone, with positive duration and literal phase closure.

The positive compiler is in `dependencies/positive_planar_PROOF.md` (SHA-256 `e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065`), §§2–7. The signed micro-shear subdivision, SL₂ factorization, small centered dilation, and guard-pullback mechanism were inspected. Its center margins survive arbitrarily large rational parameters because its subdivisions fix the center at every completed step. The retained identity factorization makes F(I,1) a nonempty timed word; its time lower bound is therefore not lost in a zero-parameter case.

The full GL₂ extension and singular obstruction are in `dependencies/invertibility_GL2_PROOF.md` (SHA-256 `dc97e30c56817370138d6be760d44a5df031743a0ee1011cca39381b67bb0cec`), §§2–5 and 7. Its transverse-flight inverse makes the complete, translation-quotiented section map invertible. Its seven-event J primitive has one marker-only collision and a strict center chamber. For negative determinant the composition is the positive realization of J⁻¹C, followed by J, with fresh phases.

This audit does not re-certify the unrelated spectral-classification corollary in the positive dependency. It is not needed for the new construction. The new contributions checked here are the outer-marker operation, its 20-event recentering, compensated scale shear, assembly of the full fixed-center family, general active-spectrum clock statement, and 44-event mixed-clock family.

## 3. Eight-event outer-marker chronology for every rational v>0

Source: `PROOF.md` lines 49–87.

Let h=(v−1)/(v+1). After launch at (D,D), the moving marker follows R(t)=D+h(t−D). The messenger returns to Y at t_b=2D−y and then follows y+t−t_b. Solving these two affine equations gives

- t*=(v+2)D−(v+1)y
- d=R(t*)=y+v(D−y)

These identities were independently solved and checked symbolically, rather than accepted from the event table. The full flight list is

x, y−x, D−y, D−y, v(D−y), v(D−y), y−x, x.

It is strictly positive exactly under the stipulated ordered section 0<x<y<D and v>0. The event partners X,Y,R,Y,R,Y,X,L are correct. At the middle Y bounce the moving R lies above Y by 2v(D−y)/(v+1)>0. Throughout its motion, R lies between its endpoints D and d, both greater than y. It therefore cannot meet any stationary marker. The outgoing messenger separates from it because −1<h<1; the returning messenger catches it with speed difference 1−h>0. Following restoration, the messenger travels strictly inward past the two listed spectators. There is no unlisted spectator in the Y–R interval and no remote moving pair.

This proves sufficiency and excludes simultaneous remote events. Necessity here is simply the prescribed initial ordering: no extra guard arises. The total duration is 2[D+v(D−y)]. The v=1 case is sound: a temporary label may have speed zero because its actual partner still has speed ±1. No event is removed or collapsed.

## 4. Twenty-event recentering and the exact raw guard

Source: `PROOF.md` lines 89–128.

For an anchor scale q→αq, the target speed (α−1)/(α+1), principal times q,2q,(2+α)q,2(1+α)q, and spectator times p,2q−p,2q+p,2(1+α)q−p agree. The strict hypotheses 0<p<q and p<αq put every spectator time in its required principal-time interval. For example, 2q+p<(2+α)q is precisely p<αq. Monotone target motion between strictly ordered endpoints excludes marker-only contacts. Thus endpoint ordering is sufficient, and failure forces an extra/coincident contact before the claimed restoration or collapses the required order.

Set s=(v+2)/3. For s<1, X then Y is correct: sx<x<y<d, and sx<sy<y<d. For s>1, Y then X is correct precisely when sy<d: Y stays above x and below d; afterward x<sx<sy. At s=1 the two identity scales remain genuine 4- and 8-event blocks. Consequently the exact raw cone is

x>0, y−x>0, D−y>0, d−sy>0,

with d−sy=vD+(1−4v)y/3. For v≤1 the last row follows from d>y≥sy; for v>1 it is essential. Equality places Y's intended restoration at the stationary R, a nonbinary simultaneous contact. If sy>d, some wrong contact necessarily precedes the prospective endpoint. This necessity argument stops at the first obstruction and does not assume a fictitious continuation after it.

The raw duration is 2[D+v(D−y)]+2(1+s)(x+y), because the incoming distance of each inner target is its original x or y even though the other target may already have changed. The count is 20 events and three temporary marker labels. At x=D/3,y=2D/3, d=sD and d−sy=sD/3>0. The centered matrix and its determinant are exactly

N_v = [[s,0,1−v],[0,s,(v−1)/3],[0,0,v]],  det N_v=vs².

## 5. Compensation, arbitrary rows, and exact full lifts

Sources: `PROOF.md` lines 130–172.

The lower-right block A_v is invertible for every v>0. Its compensation is F(C_v,1/s), where C_v=sA_v⁻¹ has determinant s/v>0. Because F(C_v,1/s)=diag(1/s,A_v⁻¹), the product on the left of N_v is

E_(0,k)=[[1,0,k],[0,1,0],[0,0,1]],  k=3(1−v)/(v+2).

There is no lost overall scalar. Independently, k+3=9/(v+2)>0 and 3/2−k=9v/[2(v+2)]>0, and dk/dv=−9/(v+2)². The inverse v=(3−2k)/(3+k) gives exactly the rational interval (−3,3/2). Subdivision into |δ|≤1 therefore suffices for every rational coefficient, and all factors fix the center.

For r=(a,b)≠0, B=[[b,−a],[a,b]] has determinant a²+b²>0. The actual chronological order is F(B,1), E_(0,1), F(B⁻¹,1). Multiplying in reverse chronological matrix order gives diag(1,B⁻¹) E_(0,1) diag(1,B)=E_r; specifically, the new top row is the second row of B, namely r. The order and row choice are correct.

Finally F(A/s₀,s₀) E_(b/s₀)=[[s₀,b],[0,A]]. This realizes the requested homogeneous representative itself. A negative determinant of A is handled by the inherited J suffix, not by changing the projective lift or negating a physical scale. For b=0 the shear prefix can be omitted because the retained final F word is still nonempty.

## 6. Chambers, phases, and finite deterministic completion

Sources: `PROOF.md` lines 174–207; full `RULES44.json`; dependency phase arguments.

For chronological blocks (M₁,G₁),…,(M_q,G_q), the precise domain is the conjunction G_jM_(j−1)…M₁z>0. The proof correctly retains every compensation/compiler guard. Sufficiency is blockwise; necessity uses the first invalid block after a valid prefix and that block's first-failure theorem. It does not infer an exact physical chamber from endpoint compatibility alone.

Each completed block carries the center to a positive multiple of itself. Thus every pulled-back row is strictly positive there. Finitely many strict rows leave an open neighborhood, and the first block's ordering rows imply 0<x<y<1 at D=1. The chamber is consequently a nonempty, bounded, open rational polygon, not merely an arbitrarily selected smaller safe polygon. Its final denominator is positive because its final physical section is ordered.

Fresh messenger labels distinguish each messenger-involving event; fresh target labels distinguish launch/restoration, including speed-zero identity operations. All new and positive-compiler target speeds are in (−1,1), so each explicit input and output pair has distinct speeds. At J's unique marker-only event the messenger label stays unchanged. Copying J's fast temporary X label makes that input set unique. The resulting phase count m−r_J is correct; assigning one new messenger phase at a remote event would have been invalid.

The 44-rule table was checked in full. Its ranges are: outer operation 1–8; inner Y scale 9–16; inner X scale 17–20; global X scale 21–24; global Y scale 25–32; global R scale 33–44. Its temporary speeds are h, p=(v−1)/(v+5), p, −h, −h, −h, exactly the intended scale velocities. For v>1, 0<h,p<1, so all pairs are distinct-speed. Every temporary appears once as output at launch and once as input at restoration. Every rule has Q_j→Q_(j+1 mod 44); the final Q₀ has speed +1. There are 44 distinct input sets, 44 phase labels, four stationary labels, six temporary labels, hence 54 meta-signals. All 44 rules consume and emit two signals.

Identity completion for other admissible collision sets is finite and deterministic. It preserves number and does not turn an extra contact into a member of the chosen complete word. Five live signals is a population statement, not a claim of five labels or five speeds, nor a claim that the global rule map is reversible.

## 7. The coefficient-one count

Source: `PROOF.md` lines 209–240; positive dependency §§3–6.

For v=1/4, s=3/4 and C_v=[[1,1],[0,3]], factor off diag(3,1). The determinant-one factor is [[1/3,1/3],[0,3]], and V(6)U(1/3)V(−2) equals that matrix. Thus chronological shear parameters are −2,1/3,6 with subdivision counts 8,2,24. Hence K=34, four transfers, three shear blocks, and H=8 determinant-dilation pieces.

Fixed-scale compensation: 18·34+3·4+14·8=736 events. Add 24 for global factor 4/3 and 20 raw events: **780**. Temporary labels: 3+4·34+3·8+3=**166**. Supplied guards: 4+(4·34+4·3+8·8)=**216**. Meta-signals: 780+166+4=**950**. These exact counts assume the displayed inherited compiler, including its retained zero words and redundant guards. They are not lower bounds or optimization claims.

## 8. Repeated validity and the active-cyclic clock theorem

Source: `PROOF.md` lines 242–273.

Literal phase closure makes infinite validity exactly G N^n z>0 for all n≥0. With z=(1,w), these are countably many strict rational affine half-planes in w. Their intersection is convex and contains the center, but need not be open. The accepted equality boundary in the later example does not contradict strict one-pass guards.

The macro duration is a homogeneous rational row ℓz because all denominators in its fixed collision equations depend on fixed label speeds, not input positions. The claimed uniform lower bound 2D is justified for this particular compiler: if b≠0 its first block F(B,1) has that lower bound; if b=0 its final retained F block does. The inherited negative-determinant extension still starts with a positive compiler. For the upper bound, finitely many linear event-time and position forms are bounded on the closure of the normalized input triangle. Position between successive endpoints is affine in time and therefore obeys a bound of the same kind. A fixed constant C gives duration and position bounds proportional to incoming D.

For an infinitely valid orbit, |ξ_n| and |η_n| are bounded by constants times D_n, because the section is ordered. Therefore ΣD_n<∞ implies N^nz→0. Conversely, z is a cyclic vector for V_z=span(z,Nz,N²z), which is invariant by Cayley–Hamilton. If N^nz→0, no nonzero component in a generalized eigenspace with |λ|≥1 can occur; since z cyclically generates V_z, every eigenvalue on that restricted space has |λ|<1. Jordan terms then obey polynomial-times-geometric decay and are absolutely summable. Thus the two directions of

Zeno ⇔ ΣD_n<∞ ⇔ N^nz→0 ⇔ every eigenvalue of N|V_z has modulus <1

are justified. Importantly this assertion is conditional on infinite validity and on the proved positive macro-time comparison. It is not an unconditional classifier of every initial vector or every finite signal word.

For rational N,z, the cyclic space has a rational basis, the restricted I−N is invertible in the Zeno case, and the sum is rational. The restriction is necessary: inactive unit modes can make the ambient inverse undefined. The position bound proves convergence of all five signals to L during the Zeno execution; it provides no continuation beyond the accumulation.

## 9. The exact 44-event mixed-clock family

Source: `PROOF.md` lines 275–313; `SECTION44_AND_GUARDS.json`.

For v>1, let r=(v+2)/(3v)∈(1/3,1). A global factor 1/v after the raw block gives (D',x',y')=(D−ay,rx,ry), a=(v−1)/v. The global contraction order X,Y,R adds no guard: each inner neighbor has already been contracted and each outer neighbor has not. The fourth raw guard divided by v is exactly D'−y'>0.

Because 1−r=2a/3, c=D−3y/2 is invariant, and the algebraic powers are x_n=r^nx, y_n=r^ny, D_n=c+(3y/2)r^n. The raw guard at macro n is c+(y/2)r^(n+1)>0. If c≥0, it and all section-order rows are strict at every finite n. If c<0, that expression eventually becomes negative; an earliest failed guard exists, and validity fails there without any assumption about later physical evolution. Thus infinite validity is exactly **D≥3y/2** on the initial ordered cone, including equality.

The sum of three block durations is exactly the displayed T in equation (14). Its outer part alone is greater than 2D. If c=0, all sections scale by r and T_n=r^nT₀, yielding finite total T₀/(1−r). If c>0, D_n≥c and every macro takes more than 2c, yielding divergence. Hence the same fixed machine and complete word genuinely have both behaviors. The eigenvalues 1,r,r give the same conclusion: c detects the active unit mode. The equality boundary is Zeno despite all one-pass inequalities remaining strict at every finite iterate.

## 10. Native positive-integer gap certificates

Source: `PROOF.md` lines 315–325; `NATIVE_GAP_CERTIFICATES.json`.

With positive integer inputs g₁,g₂,g₃ and x=g₁,y=g₁+g₂,D=g₁+g₂+g₃, initial ordering is automatic. Set L=2g₃−g₁−g₂ only as an abbreviation. Then 2c=L. Over the declared integer domains:

- (L−w+1)²=0 with w>0 has the single possible witness w=L+1, admitted exactly when L≥0
- L²=0 has no witness variable and admits exactly L=0; an admitted input has its one empty witness tuple
- (L−w)²=0 with w>0 has the single possible witness w=L, admitted exactly when L>0

All are single degree-two polynomials in the native inputs and stated witness variables. Witness counts **1/0/1** and uniqueness are exact; there are no hidden alias variables. The first implication uses integrality: L>−1 is equivalent to L≥0 for integer L, not for arbitrary real or rational L. No general Diophantine classification follows from this elementary family.

## 11. Scope beyond the central ray

Source: `PROOF.md` lines 327–347.

The fixed-center statement is genuinely proved. A general compatible GL₃ matrix remains outside it unless an additional construction is supplied. The displayed rational translation T gives T⁻¹MT=[[λ,c],[0,B−pc]] for an appropriate rational eigenray, but this only changes encoding; it does not physically realize T or T⁻¹ in the original marker coordinates.

The positive gap matrix [[1,1,1],[1,2,1],[1,1,3]] has determinant 2 and characteristic polynomial t³−6t²+8t−2. Its only possible rational roots ±1,±2 all fail, so it has no rational eigenray. Its centered conjugate is correctly displayed. It is an uncovered compatible matrix, not an impossibility certificate for other constructions. No novelty, priority, minimality, general universality, or arbitrary-original-coordinate GL₃ claim should be inferred.

## 12. Primary-literature cross-check

The following are direct checks of primary text, not reliance on the packet's bibliography. They establish precedents and delimit attribution; they do not establish the new five-live-signal compiler.

1. Mestl, Lemay and Glass, *Chaos in high-dimensional neural and gene networks*, Physica D 98 (1996), printed pp.35 and 40, equations (2.3)–(2.4) and (4.2): fractional-linear wall/cycle maps and the domain restriction selecting the intended exit itinerary are present. The normalized algebra is therefore not new in isolation. [Institution-hosted article](https://www.mcgill.ca/physiological-dynamics/sites/physiological-dynamics/files/chaosinhigh_1996.pdf)
2. Alishah, Duarte and Peixe, *Asymptotic Poincaré Maps along the edges of Polytopes*, manuscript pp.21–23, equations (5.1)–(5.3), Proposition 5.4, the reversed-flow inverse paragraph, and Definition 5.7: oblique constant-flow maps and pulled-back itinerary cones are explicit. Their flow setting differs from a signal compiler. [Primary manuscript](https://arxiv.org/pdf/1411.6227)
3. Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model*, §§3.1–3.2, manuscript pp.4–9, especially scale-relative registers and Figure 6: signal-distance arithmetic and multiplication speeds are explicit. The encoding has additional signals and variable registers; its arithmetic precedent does not prove this population-preserving five-signal section theorem. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf)
4. Becker et al., *Abstract Geometrical Computation 10*, §2, Definitions 1–2, PDF pp.4–5: finite labels have assigned constant speeds; input and output collision sets have distinct speeds; deterministic rules and positive-next-meeting dynamics match the conventions used here. Equal speeds for different labels in unrelated phases are allowed. [Primary manuscript](https://arxiv.org/pdf/1804.09018)
5. Belgacem, Edwards and Farcot, *Computer-aided analysis of high-dimensional Glass networks*, §III, manuscript pp.7–9, equations (6)–(12): fractional-linear composition, positive denominators, and strict pulled-back itinerary inequalities are explicit. No associated software was executed. [Primary manuscript](https://arxiv.org/pdf/2411.10451)
6. Becker et al., *Abstract Geometrical Computation 8*, §2.3, Lemmas 1–2, manuscript pp.11–12: affine changes of speed values and common spatial changes preserve diagram structure. They do not supply an arbitrary affine transformation of this two-coordinate marker shape. [Primary manuscript](https://arxiv.org/pdf/1307.6468)

The literature wording in the packet is appropriately limited. This was a bounded verification of cited precedents, not an exhaustive novelty search.

## 13. Corrections and publication advice

**No theorem, formula, event, guard, phase, count, clock boundary, or native-witness correction is required.** The frozen version is accepted with its explicit dependencies and qualifications.

One optional evidence-label precision: the author's list of “36 symbolic checks” consists of 34 symbolic equality checks, a finite rational-root-candidate check group, and a finite subdivision-fixture group. “36 named static checks” is the more literal label. The all-parameter arguments are supplied by the conventional proof, so this is a documentation distinction, not a mathematical defect and not a reason to alter the frozen packet.

Retain the restrictions already stated: exact constructed chamber rather than prescribed arbitrary guards; matrix-dependent finite machine rather than one universal unchanged rule table; full fixed-center homogeneous family rather than arbitrary original-coordinate GL₃; infinite-validity hypothesis for the clock theorem; positive-integer domains for native certificates; no continuation through accumulation.
