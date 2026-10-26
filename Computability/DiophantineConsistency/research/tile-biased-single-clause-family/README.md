# A clause at1006 by fixed tile-dependent parity corrections

This CODE-FREE author proposal gives a complete conditional native/P66
family at radix exponents b=49 and53. It retains the fifteen-positive,
66-operation, degree157 front and the entire admissible942-tile language.
All new finite controller requirements remain UNKNOWN. No L, auxiliary
prime, residue, tuple or new endpoint is selected; no application, helper,
array, import, AST, Lean, TeX/PDF or rendering program ran. No maintained
or frozen predecessor is changed. No measured raw/text/page gain is claimed.

ROOT supplied the conceptual lead, count-phase order and general-controller
suggestion. The author `/root/alternate_encoding_research` performed this
whole hand audit and exposition. Neither contributor is an independent peer.
Two full independent ordinary reviews and separate finite acceptance remain
necessary before using this as an unconditional new equation instance.

## 1. Retained explicit language and preserved hand corrections

The whole immediate ordinary source is
`../parity-clause-independent/PROOF.md`,653lines, SHA256
`c4ce22beb76dc7d39d17d83fe8be2fc8f6a20057ee5fd576556f173c70400b22`.
The entire942-tile table,430-action closed decoder, complete436-character
seed and ordered62-character historical alphabet are explicit in
`../../candidates/one-page-parity-clause2999/equation.tex`,138lines, SHA256
`19640866911359c6d3f0e134b16fb2bd0435cbec09713f6557b01a0661178334`.
These exact printed finite data are retained, not replaced by an unspecified
program index or external numeric coefficient array. This research adapter
does not prepare a new page; any decimal-seed typesetting is separate.

Write its tiles t_j=(w_j,n_j,p_j,s_j),0<=j<=941. Relative to the original
943 table the exact map is g(0)=0,g(j)=j+1 for1<=j<=941, deleting precisely
the already forbidden old selector1. Initializer928 is(3,436,4,4).
The complete underlying selector language, old colors, seams, signals,
marked computations, syntactic-refutation calibration and independently
cofinal one-Start rectangles are those of source section1, unchanged.

Set logical complemented components

    wbar_j=255-w_j, nbar_j=511-n_j,
    pbar_j=255-p_j, sbar_j=511-s_j.

Every genuine horizontal/vertical logical color is respectively6..255
and73..511. Start0 is(253,76,252,510) in this order. Tile941 is
(251,74,253,74), with logical south bit0 zero.

The initial ROOT shorthand called the969 lane physicalW and incorrectly
identified it with the FIRST packed component. This was corrected BEFORE
source authoring:969+i carries bit17+i, so the THIRD component pbar is
biased;978+i carries the unchanged first component wbar. All formulas
below use exact coordinates/components rather than that shorthand.
Also, the one-hot reflected bound below applies ONLY to fields h<=1005:
at higher fields an odd selector coefficient can have a LABEL predecessor.
No global one-hot bound is asserted. These are preserved hand-scope
corrections, not source/application failures or repairs of a predecessor.

## 2. Every new fixed arithmetic bit recipe

For each member choose FIXED b in{49,53} and FIXED odd L>=2031. Define

    rho=2^b, M=2^46, mu=M-2, d=bL,
    B=rho^L, beta=B-1, G_m(x)=sum_(r=0)^(m-1)x^r.

They are fixed family parameters, never Diophantine unknowns. Section10
states the unresolved finite requirements; no existence assertion is made.
Every coefficient recipe below uses fixed finite sums/floors and arithmetic.

For a nonnegative fixed integer z define

    bit_i(z)=floor(z/2^i)-2floor(z/2^(i+1)).

For 0<=j<=941 and any h in960..968,987..994 or{1005}, put

    epsilon_h(j)=floor((h+877-j)/942).

On precisely these ranges this is0 or1, equivalently the indicator of
0<=1006+j-h<=941. Define the actual encoded components by

    p_enc_j=sum_(i=0)^7
      [bit_i(pbar_j)+epsilon_(987+i)(j)
       -2bit_i(pbar_j)*epsilon_(987+i)(j)]*2^i,
    s_enc_j=sum_(i=0)^8
      [bit_i(sbar_j)+epsilon_(960+i)(j)
       -2bit_i(sbar_j)*epsilon_(960+i)(j)]*2^i,
    u_enc_j=wbar_j+2^8*nbar_j+2^17*p_enc_j+2^25*s_enc_j.

The bracket is the exact XOR of two fixed Boolean data bits. No variable
XOR, new unknown or hidden program is introduced. wbar/nbar stay unchanged;
in particular nbar>0 proves0<u_enc_j<2^34. For each selected j the map
between logical and encoded label bits is an involution. It is a bijection
on selector-plus-label graphs, NOT a global permutation of individual
color values. Edge recovery is proved through the corrected parities below.

The complete physical set is

    Es={0..941} union{942..950} union{960..968}
       union{969..976} union{978..985} union{977,1005}.

All978 physical positions are Boolean. Dummy977 and marker1005 have zero
coefficient. For EVERY0<=e<=3296 define

    c_j=1+2^12*(2^34-u_enc_j), j=0..941;
    c_(978+i)=2^(12+i), c_(969+i)=2^(29+i), i=0..7;
    c_(960+i)=2^(20+i), c_(942+i)=2^(37+i), i=0..8;
    c_e=0 at every other index.

There are976 nonzero coefficients. Each selector is odd,1 mod4096 and
strictly below M. Labels are even, sum to M-4096 and occur at34 distinct
positions. Thus the COMPLETE coefficient sum is less than943M, without
evaluating any array or importing an old numerical sum.

## 3. Full coherent tuple and all padding, for both exponents

Define the physical/weighted polynomial pair

    Psi(x,t)=x^969*(x^9+t^17)*G_8(tx)
             +t^8*x^942*(x^18+t^17)*G_9(tx)+(2-t)*x^1005,
    Phi_enc(x)=sum_(j=0)^941 [1+2^12*(2^34-u_enc_j)]*x^j
               +2^12*Psi(x,2),
    DC=rho^18+sum_(e=0)^985 c_e*rho^(1006-e),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es)rho^e,
    Ccore=rho^960*G_9(rho)+rho^987*G_8(rho)+rho^1005.

There is NO bare marker monomial in DC or K. The first reflected exponent
is1006-985=21, above bare18. Every formal coefficient986..3296 is zero.
Psi(x,1) includes the marker physically; Phi_enc omits its weight.

Use these complete padding choices:

|b|Full fields|Number m_b|Final field|Low bits r_b|Total padding|
|---|---|---:|---:|---:|---:|
|53|2012..2028|17|2029|13|17*53+13=914|
|49|2012..2029|18|2030|32|18*49+32=914|

Put a_b=2012+m_b and

    Z_b=(rho-1)*rho^2012*G_(m_b)(rho)+(2^(r_b)-1)*rho^(a_b)
       =2^(r_b)*rho^(a_b)-rho^2012,
    MF_native=4+mu*rho^1006+Ccore+Z_b,
    MF_source=MF_native+beta.

The entire compact four-port recipe is therefore

    beta=B-1,
    K=rho^18+rho^(L+9)+rho^1006*Phi_enc(1/rho),
    MC=beta-rho^977-G_942(rho)-Psi(rho,1),
    MF_source=B+3+mu*rho^1006+Ccore
              +2^(r_b)*rho^(a_b)-rho^2012.

All reciprocal exponents in nonzero summands are positive, so K is an
integer. The native-source mask shift is exactly ONCE.

## 4. Scalar interface before any native interpretation

The clause mask tests bits1..45:45 bits. The17 label tests, marker test
and origin test add19, so core population64 plus padding914 equals978.
All masks are disjoint. MC clears exactly978 physical bit0s, including
both zero-weight fields; it permits neither digit2 nor3 at dummy977.
Consequently

    pc(MC)=d-978, pc(MF_native)=978,
    MC=2 mod4, MF_native=4 mod8,
    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, MC<beta<MF_source<2beta.

The high padding digits fit because a_b<L. Every DC coefficient is below
rho, and reflected exponents are distinct from bare18. The scalar bound
2mu+4=2^47<rho holds for BOTH49 and53.

The retained positive arithmetic/inverse-population contract now gives
q=B^N, J=(q-1)/(B-1), positive C,F, F+C<q,0<F<q-1 and actual masks

    (C-1) AND(MC*J+1)=0,
    F AND(MF_native*J-1)=0.                         (1)

Thus C has Boolean rho digits exactly on Es, Start selector0 is forced
at the first origin, and there is no forbidden new selector. All absent
positions are zero. No tile count, label interpretation or alignment has
yet been used. Transport is a cyclic binary rotation because the same
outer recovery gives X=2^R, q=2^(dN), w=2^(R-dN).

## 5. Global cyclic carries and count BEFORE phase or label recovery

At every field each coefficient in the single band occurs at most once.
Bare18 and DR add at most two Boolean units. Every original C digit is
Boolean, so in each fractional phase p=0..b-1 the temporal digit is
either0 or2^p, at most rho/2, with NO spill to another field. Thus

    raw_total<943M+2+rho/2.

The following cyclic carry boxes are sufficient:

|b|M/rho|Carry bound k_b|Bound needed for invariance|
|---|---|---:|---|
|53|1/128|9|943M+rho/2+11<10rho|
|49|1/8|119|943M+rho/2+121<120rho|

Both inequalities follow directly from rho=2^b. The monotone cyclic map
k_h->floor((raw_h+k_(h-1))/rho) preserves0..k_b; iteration from zero
stabilizes on this finite box. Cyclic telescoping identifies the transport
residue. Strict F in(1) selects its representative in soundness; the
converse constructs it before imposing strict F. No carry-free conclusion
or tile interpretation enters this argument.

At the sole clause1006, bare predecessor988 and spatial predecessor997
are absent. Its non-temporal value is exactly

    Acl=n+4096Q,
    Q=sum_j(2^34-u_enc_j)*x_j+W, 0<=W<2^34,
    n=sum_j x_j<=942.

Incoming carry k<=k_b and temporal term tau*2^p have tau Boolean. If
p<12, n+k+tau*2^p is at most2999 for53 and3109 for49, both below4096.
If p>=12, the temporal term is a multiple of4096 and n+k<=1061<4096.
The tested bits1..11 therefore force the relevant small sum to0 or1.
In EVERY phase this proves n<=1, and occupied n=1 forces k=0.
For1<=p<12 it also forces tau=0. Labels are NOT yet decoded when p>=12.
This limited conclusion is all the next stage uses.

## 6. The LOCAL reflected bound and phase recovery

For any field h let the complete reflected contribution be

    E_h=sum_(f in Es)c_(1006+f-h)*x_f,

with out-of-range coefficients zero. If h<=1005 and c_(1006+f-h) is a
selector coefficient, then f<=940: its predecessor is a SELECTOR, not a
label. There is at most one such selected f by section5. All other
nonzero coefficients are distinct label weights. Hence ONLY in this
low band

    0<=E_h<2M.

Adding at most two bare/spatial units, rho/2 and incoming k_b stays below
rho: for49 use2M=rho/4, for53 use2M=rho/64. Thus EVERY outgoing carry
through field1005 is zero in all b fractional phases. This includes all
copy tests and the clause predecessor1005.

Since every selector coefficient is odd and every label coefficient even,
the low reflected parity in an occupied cell of selected type j is

    E_h=1_(0<=1006+j-h<=941) mod2.

For an empty cell it is zero. At marker1005 this is
bmark(j)=1 for j<=940 and0 for j=941. Its bare/spatial predecessors987
and996 are absent. The forced Start cell has j=0, hence odd E_1005;
the marker mask and zero incoming carry require an odd temporal digit.
Every phase p>0 makes all temporal digits even. Therefore p=0, before
any label recovery, occupation or known marker value.

## 7. Full physical label decoding and every field offset

Temporal digits are now Boolean. At clause1006 the small sum n+k+tau
is below4096, so the count masks give n+k+tau in{0,1}. Occupied means
n=1,k=tau=0. Bits12..45 give Q=0 mod2^34. For n=0 this forces W=0;
for n=1,0<Q<2^35 forces Q=2^34 and W=u_enc_j. Thus every cell is
decoded with all34 ENCODED labels before field alignment is attempted.
The marker and dummy remain independent Boolean bits.

At target960+i the complete non-temporal parity is the current encoded
south bit plus epsilon_(960+i)(j), hence the LOGICAL south bit of j.
At target987+i it is the current encoded THIRD-component bit plus
epsilon_(987+i)(j), and the spatial neighbor's UNCHANGED first-component
bit. The only bare/spatial identities used here are

    target960+i: current942+i + E_(960+i), i=0..8;
    target987+i: current969+i + spatial978+i + E_(987+i), i=0..7;
    target1005: E_1005.

The unwanted temporal-copy spatial sources951..959 are absent; spatial
test positions987..994 are absent. All low incoming carries are zero.

For Start j=0 all nine south biases are1, so physical south encodes1,
but the corrected parities are exactly logical510: bits1..8 require odd
temporal digits at961..968. Marker parity gives r=1005-f for some f in
Es, where r is the remaining field offset. Either f=1005 and r=0, or
20<=r<=1005. If r>961, test961 wraps to L+961-r>=L-44>1005, absent.
If r=20, tests961/962 require selector941 and physical south bit0 in
that same source cell. The decoded tile941 has bias epsilon_960(941)=0
and logical south74 with bit0 zero, contradiction. If21<=r<=961,
tests961/962 require two distinct selectors in0..941 in the SAME source
cell, contradicting n<=1. Thus r=0.

## 8. Logical edges, marker, every reset and fresh words

The17 aligned parity equations are now EXACTLY the original logical
temporal south/north and spatial third/first edge equalities. This also
holds with empty cells: all their physical labels and reflected selector
parities vanish. Logical genuine colors are positive, so spatial equality
propagates occupation from forced Start through the one-cell rotation
cycle. Every cell is occupied. The tile-dependent physical encoding does
not need physical colors to be positive or to form a global color map.

The marker equation is

    a_(temporal predecessor of i)=bmark(tile_i).

It is not a shifted-Start indicator: all selected types0..940 contribute1,
type941 contributes0. The sole predecessor1005 is E_1005 plus its
temporal marker, with no bare/spatial term; its outgoing carry is zero
by section6. The aligned clause1006 has no temporal source because1006
is absent from Es, hence actual value M+1 in each occupied cell.

The complete last product field2011 is c_0*x_1005. Since c_0<M, adding
incoming k_b still resets carry. All later fields2012..L-1 are actual
zero. This proves EVERY914 padding test for BOTH rows of section3 and
the reset across every cell origin. At origins only temporal selector0
contributes. Logical Start north76 differs from south510, so temporal
stride is nonzero; canonical one-Start words satisfy all origin masks.
Inverse encoded-label decoding and g recover a genuine old admissible
marked computation and its complete syntactic refutation.

Conversely a refutation supplies fresh independently cofinal one-Start
helical rectangles in the retained logical language. Encode each selected
tile with its exact new p/s bits. Set marker a_j=bmark(tile_(j+width))
cyclically, initially set dummy977 to zero, and construct the cyclic word.
Every simultaneous Boolean subset of safe dummy bits preserves selector
counts, decoded labels, all corrected edge parities, the marker equation,
all resets and masks. Its occupied clause ensures F>0. For EVERY subset,

    0<F<q/rho<q/7, 0<C<q/rho^(L-1006),
    2C+F<q*(1/7+2/rho^(L-1006))<q/3,
    alpha=q-F-C>0, F<q-1.                          (2)

## 9. Actual rank, ordinary increments and full odd phase

Let t=dN,q=2^t, S_word=(C-1)+qF and
T_mask=(MC*J+1)+q*(MF_native*J-1). Their exact populations are
(d-978)N+1 and978N+1, including10->11 and100->011 origin changes.
Disjointness(1) gives pc(T_mask)=t+2. The ACTUAL rank with one mask shift is

    R=[q(q-F)-C]*(q²-1)+(MC+q*MF_source)*J
     =(q²-1-S_word)*q²+(S_word+T_mask).

Thus pc(R)=3t+2. Independently C=J=1 mod4,F=0 mod4 give R=3 mod4.
For safe j with j+1<N and j+width<N, let deltaC=rho^977*B^j and
deltaRaw=(K+B^width)*deltaC. Current-cell exponents are at most1983,
spatial exponent986 and temporal exponent977. DC coefficients are below
rho and distinct; coincident later cells have distinct residues986/977.
There is no collision or wrap. Therefore0<deltaRaw<q/rho²<q/7 and(2)
gives F_old+deltaRaw<2q/7<q-1 at every intermediate subset. Canonical
representatives obey the ordinary equality F_new-F_old=deltaRaw. Hence

    deltaR=-Gamma*B^j,
    Gamma=rho^977*(q²-1)*[1+q*(K+B^width)].         (3)

For either odd b, odd L and the odd N chosen below, t is odd. Together
with R=3 mod4 this makes both R-t and R-3t even. The retained P66
converse's two squares are available in BOTH odd t mod4 phases.

## 10. Sufficient WHOLE-d controller, without squarefreeness

For each exact fixed b,L,K define H_ctrl=1+B*K+B². The finite condition
P_bias(b,L) is the existence of an odd PRIME lambda>d, kappa=lambda-1,
such that

    B^kappa=1 mod the WHOLE d,
    gcd((B²-1)*H_ctrl,d*lambda)=1,
    v_lambda(B^kappa-1)=1.

All are finite explicitly stated requirements on the NEW complete K.
No L, lambda, exact order, spacing or H residue is selected or evaluated.
For49, d=49L is not presumed squarefree. No old certificate transfers.

Choose independently cofinal width=lambda^rw,height=lambda^rh with
height>lambda,N=width*height>d*lambda². Put T_orbit=N/lambda,C0=d*lambda;
then T_orbit>C0 and width<T_orbit. Powers of lambda are1 modkappa, so
q=B^N and B^width reduce to B modulo WHOLE d and modulo lambda. Thus
the two non-2 factors of Gamma reduce to B²-1 and H_ctrl, and(3) is a
unit modulo the WHOLE dN. This uses the stated whole-d congruence/units,
not inference from residues at only its distinct prime divisors.

LTE gives order T_orbit for B^kappa modulo lambda^n. It is1 modulo d;
CRT therefore identifies its FULL orbit modulo dN as

    {1+C0*z:0<=z<T_orbit}.

Indeed this set has T_orbit elements and the same two congruences; the
order proof is exact. No step uses squarefreeness of d.

Every target modulo dN is a Boolean subset sum of
{B^(2+kappa*j):0<=j<T_orbit} together with B³. Normalize by B^-2 and
choose epsilon0/1 so subtracting epsilon*B is nonzero modulo lambda.
Its least representative a0 modulo C0 obeys1<=a0<C0<T_orbit and
gcd(a0,T_orbit)=1. Write the target a0+C0*u, solve
a0*z0+a0*(a0-1)/2=u modT_orbit, and sum a0 consecutive distinct orbit
coordinates, adding B³ iff epsilon=1. The largest cell index is
2+kappa*(T_orbit-1)=N-T_orbit-lambda+3; both its one-cell and width
translates lie below N. Cell3 is distinct and safe; all avoid the origin.

Apply this subset to(R0-d*width)*Gamma^-1 modulo dN. It gives ACTUAL
R=d*width mod dN, while all masks and slack persist. Rank growth gives
R>q(q²-1)>dN+d*width. Thus w=2^(R-dN)>B^width and
w=B^width mod(q-1). Write(K+B^width)C=F+z0(q-1), where z0>=0.
Then z=1+z0+[(w-B^width)/(q-1)]C is positive and gives Nt=1.

## 11. Whole positive P66 and both complete maps

Use EXACTLY the fifteen positive inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and the four new fixed ports.
The unchanged front is

    q=beta*J+1,C=q-F-alpha,X=wq,Y=sq³,E=XY,k=eta+zeta,
    ell=EkY,c=kY+eta,a=E+Y,H_pell=4a+3,Delta=a²+H_pell,
    D=X+ac+gamma*H_pell,
    R=[(q-1)(q-F)+alpha]*(q²-1)+(MC+q*MF_source)*J,
    V=f²*(cT-R)-c,S_aux=i*Delta*c²,
    N0=tau²-ell*(ell+k),N1=D²-Delta*c²,
    Na=S_aux²*(V²-y²)+y²,Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z*(q-1),Ns=Delta*f²-S_aux²,
    N0*N1*Na*Nk*Nt*Ns-Delta=0.

Soundness takes ALL arbitrary positive zeros. The unchanged whole scalar,
sign, main/strong/signed-auxiliary Pell and ratio/population arguments of
source sections4/12 apply to the new boxes in section4, with bridges
T_old=f*T and i_ordinary=Delta*i. They use the unresolved Nk/Nt signs
and weak C>=0 until their proper recovery stage, not an assumed accepting
history. They yield X=2^R,q=B^N,actual(1), then sections5..8 recover a
genuine refutation. P_bias is not used in soundness.

Conversely, under P_bias, fresh native sections8..10 give actual
t=dN,pc(R)=3t+2,R=3 mod4 and3q+1<=R<q⁴. The full source half-binomial/
ratio converse supplies X=2^R,Y=sq³,v2(Y)=3t with positive odd s and
positive outer witnesses N0=N1=Nk=Nt=1. Both required powers
w=2^(R-t) and X/q³=2^(R-3t) are squares by section9.

For clarity the COMPLETE private Pell reconstruction is retained. Put
A_pell=a+2 even,c=psi_(A_pell)(R) odd,m=cR,
f=chi_(A_pell)(m),i=psi_(A_pell)(m)/c². The odd-power binomial expansion
gives c² divisibility and positive odd i, with
f²=1+Delta*i²*c⁴, so ACTUAL Ns=Delta. For S_aux=i*Delta*c² set

    Vstar=chi_(S_aux)(R)/S_aux, ystar=psi_(S_aux)(R),
    Tstar=(Vstar+c+R*f²)/(c*f²).

The entire odd-index Q recurrence in the retained source gives, since
R=3 mod4 and S_aux²=Delta*(f²-1),
Vstar=-c modf² and Vstar=-R modc. With gcd(c,f)=1,f²=1 modc these make
Tstar positive integral and Vstar=f²(c*Tstar-R)-c. Its norm gives Na=1.
All five OTHER fresh factors are respectively1,1,1,1,Delta as displayed,
so their whole product is Delta and the equation vanishes. No old packed
word or private witness is carried across a changed tuple.

The exact66-operation/degree157 front facts remain uniform at these
positive ports, with nonzero selected coefficient8*beta^92. Under P_bias
and the retained explicit ordinary syntactic-refutation/foundational
calibration, ZFC proves no positive zero iff Con(ZFC). This is conditional
ordinary mathematics, not a new end-to-end Lean/internal-ZFC proof.
The fixed finite bit recipe is complete; no numerical premise, measured
size, prime-existence theorem, one-page fit or global optimum is supplied.

## 12. Prior-art and remaining checks

The retained parity2999 proof already permits EVEN reflected overlap and
uses a phase/count ordering. The present change absorbs ODD reflected
selector parity into fixed tile-specific p/s encodings and moves count
before phase, while delaying labels. The first broad search for'uenc'
matched unrelated words and truncated; it is not exhaustive evidence.
A corrected fixed-string Markdown search for bias_h/uenc_j/tile-specific/
physicalS/physicalW found no match in local research. This establishes no
global novelty claim. All new finite units/L/lambda remain unresolved;
two full nonauthor reviews and separate ROOT decisions remain outstanding.
