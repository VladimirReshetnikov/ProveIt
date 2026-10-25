# A same-six-tuple constant recipe for a possible 37-integer page

This is code-free preparation, not a page, rendered-fit claim, new equation
or executable closure. It specifies the exact source76 affine37 quartic
with the original source34 six constants. The existing original-state
722-character seed suffices; no BFS state/color/selector permutation or
transfer of a newer four-port tuple is used. No source/application program,
import, compilation, renderer, PDF tool or Lean ran. Inert text/JSON/seed
decoding, finite tile/data comparison and payload/hash reads are the scope.

## 1. Literal original seed and all430 actions

Use the ordered alphabet

    0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz

If d_i is the zero-based index of character i of the following722-character
string, counted left to right from0, define the fixed integer
Aseed=sum_(i=0)^721 d_i*62^(721-i):

    RCtYkANMQ1gmPqxuKhLmpi1mjCvu243YjyAxv9hbC2UsurRLykLFhuHVBGGUZ5whVShV0FQcVVQSR2GS6JAW1DGYxGKlA4rJavFCW5i63LLSs8xEGvWTbLjSFULVODe48Kw2ghEaa5Q9PZZVHtki7C45jfVYROOzvVT9DAGjL0BlBSHQU8WPUF3SpCkTfDQF7mUboMEAeyPWARCyClpnxtqgsit318hQgiIdKauxc6memnYNtycB0s7zK8dMgYaLRxNjlcLvJzZ9Z5wdCG3wjd5P6ZVqC2SXVaimqXrTY5dNxbCH2B5VKASp16kht0JV65p4VclYsI6zi6nIr7elpUCOX7IHdu6qKiu6Kt5MqlYZjChEzG6yW1WsPdMB7lPL3oOCFqFncCtVEMUounam1fyhduQYoTyTCIEMqcD2BPQfMVaBa9BZHQ8k7rpS3eiM7Rsak5uUsoP1Tf1uhWshndLuN8yz7UdD5QXM6AJ3ovPdWsqOHGBeRaR8kch4R9JVbkAxS2ByaeE2O6czIT0sWtpasWDdZB9FuDQUFYhSvPPPr8nSQmnMkF90CBzWkpeP81azGOWtiT2XTxpaLcR4ecaK1uZyvBleYknk6QTwECl5XJ3nJBoP4sMTGaV6unoGzq9s1KN4KtXrVRuTpi6EuqizW9njcp9Uikq1VNjVtwW1AGLJu3eaWg0EEF7vROqLuNbzEheYnyi4SORWVp

All sums and products in this recipe have fixed finite limits. Set
rem_b(x)=x-b*floor(x/b) and, for0<=j<430,

    a_j=rem_1024(floor(Aseed/1024^j)),
    u_j=rem_256(a_j), v_j=rem_2(floor(a_j/256)),
    d_j=floor(a_j/512).

Action j has original state floor(j/2), read rem_2(j), write v_j,
right flag d_j and next state u_j. Halt is215. The original first target
is93, not the BFS target1. The encoded seed is exactly the old complete
decimal seed, not another machine or a packed table supplied externally.

## 2. All943 original tiles, with no external list

For0<=q,u<=215 define

    delta(q,u)=floor((65536-(q-u)^2)/65536),
    R_q=floor((430+sum_(j=0)^429 d_j*delta(q,u_j))/431),
    L_q=floor((430+sum_(j=0)^429 (1-d_j)*delta(q,u_j))/431),
    sigR(q)=6+sum_(s=0)^(q-1) R_s,
    sigL(q)=205+sum_(s=0)^(q-1) L_s,
    head(q,b)=2q+2+b.

delta is exact equality in this range; R_q,L_q are exact membership
indicators of right/left target states. Empty sums are zero. The fixed
seed has sum R_q=199 and sum L_q=45. Form the following finite SET T
of ordered (west,north,east,south) quadruples:

| Family | Fixed indices/condition | Quadruple |
| --- | --- | --- |
| action | 0<=j<430 | ((1-d_j)sigL(u_j),head(floor(j/2),rem_2(j)),d_j sigR(u_j),v_j) |
| halt pass | b=0,1 | (0,432+b,0,432+b) |
| plain pass | b=0,1 | (0,b,0,b) |
| right reception | 0<=q<=215,R_q=1,b=0,1 | (sigR(q),b,0,head(q,b)) |
| left reception | 0<=q<=215,L_q=1,b=0,1 | (0,b,sigL(q),head(q,b)) |
| finish | z in {0,1,432,433} | (0,z,0,438) |
| fixed | four tuples | (2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0) |
| reset | z=434,435,436 | (1,438,1,z) |
| seam | a in {0,1,4},b in {0,1,2} | (a,437,b,437) |
| forbidden | one tuple | (5,0,0,0) |

The two original distinguished selectors are S=(2,435,3,1) and
Fbad=(5,0,0,0). The initializer is188=2*93+2. It is neither the
compact457 initializer698 nor the BFS initializer4.

For t=(w,n,e,s) put kappa(t)=2^30*w+2^20*n+2^10*e+s and Qkey=2^40.
Assign rank(S)=0,rank(Fbad)=1; for other t in T put

    rank(t)=2+sum_(u in T\{S,Fbad})
                   floor((Qkey+kappa(t)-kappa(u)-1)/Qkey).

All labels are below1024, so the summand is exactly1 when kappa(u)<kappa(t)
and0 otherwise. This specifies the original lexicographic order after the
two distinguished tiles, using only bounded finite arithmetic. No sort,
machine run, table oracle or state renaming is hidden in the definition.

## 3. The exact original four native constants and two cone constants

Write G_m(x)=sum_(j=0)^(m-1) x^j,
bit_j(x)=rem_2(floor(x/2^j)), and I(x)=sum_(j=0)^9 bit_j(x)*4^j.
Set

    rho=2^121, Bnative=rho^8801, beta=Bnative-1,
    offsets=(1020,1000,980,960), anchors=(1095,1096,2195,3296),
    Eset={0,...,942} union {offsets_t+2j:0<=t<4,0<=j<10}
          union {1063,1064,1095,1096,2195,3296},
    c(t)=1+2^10*[sum_(s=0)^3 4^(10s)*I(t_s+512)+4^40*G_4(4)],
    Phi(x)=sum_(t in T) c(t)*x^rank(t)
          +2^10*sum_(s=0)^3 sum_(j=0)^9 4^(10s+j)*x^(offsets_s+2j)
          +2^10*sum_(j=0)^3 4^(40+j)*x^anchors_j,
    mu=1022+2^10*G_44(4),
    Zpad=(2^119-1)*rho^8792*G_7(rho)+(2^27-1)*rho^8799.

The required SIX fixed numerals are exactly

    K0=rho^40+rho^41+rho^1100+rho^2200+rho^8802
           +(rho^4393+rho^5495)*Phi(1/rho),
    MC=beta-sum_(e in Eset\{1}) rho^e-2*rho^1063,
    MF=beta+4+mu*(rho^4393+rho^5495)
           +sum_(j=0)^9 [rho^(1000+2j)+rho^(1021+2j)]
           +rho^2195+rho^3296+Zpad,
    cone_A=2^1113, cone_B=2^666104,
    beta=Bnative-1.

The reciprocal intermediate in K0 is rational notation for an integer:
every exponent e in Phi is at most3296<4393. These definitions are finite
fixed constants, not operations on any Diophantine input. MF is already
shifted by beta; it must not be shifted again.

## 4. Exact complete equation to be printed, unchanged

The authoritative parent is source76 `positivity/quartic37.json`, SHA256
`5ed74d6b0fa9cff1a08d84c8b2b0a5e65721bccc02ee99229750113ed645f0b1`.
It has the ordered37 unrestricted integer inputs in that file and24
quadratic residuals, with polynomial sum of their squares. No input is
made positive or eliminated here. Its compact printable form uses

    J=3J3+1, q=beta*J+1, W=4*(3w3+1), k=eta+zeta,
    C=q-F-alpha, H=4a+3,
    R=(q-F)*(N-q-L)+alpha*L+(MC+q*MF)*J,
    Tcone=cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)^2,
    Pos(p,q,r)=1+p^2+q^2+r*(r+1).

The24 residuals, in the actual JSON order, are

    L-q^2+1; N-q*(L+1); X-W*q; a-E-(2v_scale+1)*N;
    E+X*(E-a); c-eta+(E-a)*k; P-k-E*(c-eta);
    tau^2-P^2+P*k-1; D-X-a*c-gamma*H; Delta-a^2-H;
    C2-c^2; D^2-Delta*C2-1; k-1-h*E-R;
    (K0+W)*C-F-z*(q-1); F2-f^2; V+c-f*o;
    V-c*j+k-1-h*E; g+V^2-y^2; I-(2r+1)*C2;
    Baux-I^2; Baux-Delta*(F2-1); y^2-Baux*g-1;
    Tcone-Pos(cone_pos1,cone_pos2,cone_pos3);
    eta*zeta-Pos(eta_zeta_pos1,eta_zeta_pos2,eta_zeta_pos3).

The37-input list and full expanded residuals remain exactly the pinned
parent's. `report/explicit_low.tex` is the retained compact display source.
The ordinary proof combines its original source34 native/controller and
Pell contract with calibrated determinant-cone witnesses, signed X residue
orientation and compatible canonical J_old=w_old=1 modulo3. It does not
substitute the newer BFS943 four ports into this six-port theorem.

## 5. Why this preserves the whole actual tuple

The base62 literal is the existing original decimal action seed exactly.
Its430 decoded original transitions equal the pinned complete transition
JSON. The finite families in section2 are the original source34 tile
construction, including both target-signal rankings and initializer188;
their complete ranked list is exactly the pinned943-tile file SHA256
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
No machine or tile-language transfer theorem is needed: the list is equal.

For every tile, I interleaves exactly its ten occupied bits into radix4.
Consequently c(t) is the same44-field source34 clause coefficient.
Phi contains exactly its selector/copy/anchor coefficients; the two dummy
coefficients remain zero. Thus the K0 expression is identically DC+Bnative*DR
with DR=rho. Eset, MC, mu, MF padding and shifted MF match the original
bounded recipe term for term. The other two constants are their literal
powers of two. All615883 raw bytes of the six existing numerals match the
source76 binding, using actual source34 raw payloads and source71 cone
payloads as byte witnesses. No six-constant substitution is being inferred
from equality of only beta or a mask.

Some source76 placed payload paths are absent in the current tree. This
note does not restore them or rely on their existence: SOURCE_PINS names
the actual equivalent source34/source71 payload files and compares their
raw SHA256 values to the exact source76 BINDING. The constants are fully
defined inline above regardless of filesystem placement.

## 6. Page feasibility and remaining checks

The full arithmetic front has24 short quadratic rows, rather than a large
expanded high-degree kernel; the seed is722 characters and the two extra
cone constants take only two short powers. A two-column Letter comparison
page looks plausible from the existing complete dense nine-integer pages.
This is not a fit, readability, actual-TeX or PDF acceptance claim. The
formula and native recipe must both be printed in full on any later page.

Before page execution, a separate held preparation must bind every printed
row to the full37-variable quartic over six free coefficient ports, every
seed digit, all430 actions and all943 ordered tiles, then reconstruct and
compare all six whole integers. An actual-TeX parser, real malformed-TeX
controls, ordinary proof closure, strict overflow/page/font checks, full
PDF text/seed recovery, deterministic rerenders and independent visual
review remain required. None has run for this opportunity. It is an
alternative degree-four/unrestricted-integer comparison, not a proposed
replacement of the maintained ten-positive page.
