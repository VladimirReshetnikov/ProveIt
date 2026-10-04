# A fixed all-length binary-word dilation relation

Own derivation and own arithmetic DAG, 3 October 2026. This document addresses raw finite-word recoding only. It does not assert a new combined universal count, re-prove the inherited 174-operation history relation, execute the frozen ant loader, or materialize the ant's periodic tile.

## 1. Interface and counting convention

The input ports are an integer radix C>=2 and a positive sentinel integer Raw. There is a unique finite binary word (d_0,...,d_{n-1}) such that

Raw = 2^n + sum_{j=0}^{n-1} d_j 2^(n-1-j), d_j in {0,1}.

Thus Raw=1 is the empty word, and leading/trailing zero symbols are retained by n. The relation produces C^n and either the forward value sum d_j C^(n-1-j) or the reversed value sum d_j C^j. Length n is existentially represented as LengthPlus-1; it is not a circuit-shape parameter. The same finite list of equations works at every length.

All quantified variables in the supplied DAG are strictly positive. Whenever a mathematical witness may be zero, the code quantifies its Plus version and subtracts 1, charging that subtraction. Each +,- costs one A; each multiplication costs one M. Equality assertions and aliases cost no arithmetic gate. Gate outputs are expressions, not separately quantified variables. Intermediate expressions may be zero or negative. Fixed numerals are initially free; the literal-1/3 adapter is addressed below.

## 2. A seven-power exponential relation

Let n>=0 and introduce the positive values

P=C^n, E=2^n, B=2^(C P+2), F=B^n,
L=2^(U+1), Y=L^D, Z=(L+1)^U.

Here U,D and all q's, o,r,x,V below are nonnegative. Impose exactly nine further equations, with s_x,s_c,s_r,s_V strictly positive:

1. F-1=(B-1)U
2. x=Raw-E
3. x+s_x=E
4. D=q_2(B-2)+x
5. Z=(q L+c)Y+r, where c=2o+1
6. c+s_c=L
7. r+s_r=Y
8. D=q_C(B-C)+V for the forward relation, or P D=q_C(BC-1)+C V for the reverse relation
9. V+s_V=P

The seven powers are replaced individually by the fixed polynomial macro of section 5. The rest of the relation is already polynomial. There are 21 additional positive witnesses: LengthPlus; P,E,B,F; Uplus,Dplus; L,Y,Z; q2plus,qCplus,qplus,oplus,rplus; the four positive slacks; Vplus; xplus. Every listed zero-capable object has its own positive adapter. In particular, merely defining x=Raw-E would not prove x>=0: the separate xplus witness is necessary and included.

### Bounds on the auxiliary radix

Write t=CP. Since C>=2 and P=C^n>=1, t>=2 and t>=C+P-1. The elementary inequality 2^(t+2)>2t+2 therefore gives B>C+P. It also gives B>2^n+2 because t>=2P>=2^(n+1). Consequently B-2>2^n-1, B-C>P-1, and B>P+1. B is a power of two, with positive exponent. No unbounded choice of a padding exponent or an unpaid length-dependent chain is used: this B is produced by one of the seven explicitly charged power macros.

## 3. Proof of the dilation theorem

The first equation gives U=1+B+...+B^(n-1), with U=0 when n=0. Every coefficient of (1+z)^U is at most 2^U<L. Therefore the base-L digit at position D of Z=(1+L)^U is binom(U,D), interpreted as zero for D>U. Equations 5--7, together with q,r>=0 and 0<=c<L,0<=r<Y=L^D, assert exactly that c is this digit. Since c=2o+1 is odd, its parity is one.

For completeness, the parity argument needs no unexpanded invocation of Lucas's theorem. Write B=2^k with k>=1. In the polynomial ring over the two-element field,

(1+z)^U = product_{i=0}^{n-1} (1+z^(B^i)).

This follows from repeated squaring, (1+z)^(2^a)=1+z^(2^a), and U=sum_i B^i. The subset exponents sum_i b_i B^i are distinct because B>=2. Hence binom(U,D) is odd exactly when

D=sum_{i=0}^{n-1} b_i B^i, b_i in {0,1}.

This automatically excludes D>U, so there is no missing bound on D. Reduction modulo B-2 gives D congruent sum b_i2^i. Both that sum and the forced x lie between 0 and 2^n-1, below B-2. Equation 4 consequently proves x=sum b_i2^i. Equations 2--3 force 2^n<=Raw<2^(n+1), and hence n is exactly the sentinel word length and b_i=d_(n-1-i).

For the forward relation, reduction modulo B-C gives D congruent sum b_i C^i. Both this latter sum and V lie in [0,P), which is below B-C. Thus V=sum b_i C^i=sum d_j C^(n-1-j).

For the reverse relation, BC is congruent to 1 modulo BC-1. For each i<n,

C^n B^i is congruent to C^(n-i) modulo BC-1.

Therefore P D is congruent to C sum_i b_i C^(n-1-i). This candidate remainder and C V are nonnegative and strictly less than C P<BC-1. Equation 8 forces V=sum_i b_i C^(n-1-i)=sum_j d_j C^j. No negative exponent is needed even when n=0.

Conversely, given any finite word and either claimed output, define all seven powers and U,D as above, take the ordinary nonnegative division quotients and remainders, and take c=binom(U,D),o=(c-1)/2. The parity identity makes c odd. The strict coefficient and remainder bounds provide positive slacks. The output-congruence quotients are nonnegative: since B>C, each B^i>=C^i, so D>=sum b_i C^i in the forward case; and C^n B^i>=C^(n-i) for each i<n, so P D>=C sum b_i C^(n-1-i) in the reverse case. The congruences therefore have nonnegative integer quotients. Every equation follows. In the empty case Raw=P=E=F=1,U=D=V=0,L=2,Y=Z=c=1; all division remainders/quotients that should vanish have valid Plus witnesses. This also explicitly verifies the empty-word corner case.

The output graph is functional, but the whole existential fiber is not unique. In particular, each paired-quotient congruence in the Pell macro admits simultaneous shifts of its two quotients. No single-fold or finite-fold assertion is made.

## 4. Exact ant-loader pair interface

Use C=G=W^576000, supplied by the periodic-board wrapper. Both nearest-head-first inputs use the standard MSB-first sentinel convention from section 1. Apply the reversed relation to RawLeft and the forward relation to RawRight. Write their outputs as P_L=G^L,V_L=sum ell_jG^j and P_R=G^R,V_R=sum r_jG^(R-1-j). Define three arithmetic outputs

A=P_L P_R,
B_out=P_R,
T=(G P_R)V_L+V_R.

Then A=G^(L+R), B_out=G^R and T=G^(R+1)sum ell_jG^j+sum r_jG^(R-1-j). T is exactly the base-G Horner value of reverse(ell),0,r. The scanned A0 primary head's nonzero bit is handled separately by the periodic wrapper, so the central digit here is deliberately 0. The name B_out is distinct from each recoder's auxiliary binary radix B.

The normal pair DAG exposes A,B,T as output ports, including three equality assertions. These are positive, positive, and nonnegative respectively. It uses 1055 operations (454 M,601 A),392 positive internal witnesses,231 equations. The ports themselves are not included among the 392 witnesses.

For direct composition under the inherited expression-node convention, inline the outputs instead: A is an arithmetic product, B_out aliases an existing positive witness P_R, and T is a nonnegative arithmetic expression. This drops the three port equations and needs no extra quantified outputs: 1055 operations,392 positive witnesses,228 equations. If all three outputs are instead separate positive ports, use Tplus=T+1, adding one A. This gives 1056 operations,392 internal positive witnesses and231 equations; quantifying the three ports externally adds exactly3 positive unknowns. The consumer must use Tplus-1, charging its subtraction if not already built. These interface choices must not be mixed when adding counts.

## 5. Explicit polynomial power macro

The following is a concrete use of the constructive Pell representation, not a use of the general MRDP existence theorem. Its source theorem is read-only mathlib4, pinned commit ac77769fabe23cb237559e7f56578dbead91499f, Mathlib/NumberTheory/PellMatiyasevic.lean, theorems matiyasevic and eq_pow_of_pell. The exact source file has SHA256 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a. No upstream Lean or arithmetic schedule is executed by this work. Source URL:

https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean

Define Pell coordinates X_j(a),Y_j(a) by X_0=1,Y_0=0 and X_(j+1)=aX_j+(a^2-1)Y_j,Y_(j+1)=X_j+aY_j. The cited constructive theorem characterizes the exact indexed pair by three Pell equations and congruences. Its second theorem recovers b^k from that indexed pair, a sufficiently large Pell-generated a, and the modulus 2ab-b^2-1. The equations below are the fully explicit positive-variable specialization of these theorems.

To assert output=b^e for b>=2,e>=0,output>=1, set k=e+1 and m=b*output. Introduce 25 strictly positive unknowns. Eleven are w,A0,T,g,x,y,u,v,s,t,B0, with a=A0+1 and beta=B0+1. Four more are D_wb,D_wk,D_yk,S, with zero-capable gaps delta_wb=D_wb-1, delta_wk=D_wk-1, delta_yk=D_yk-1 and positive S. Two are q_b,q_v. The remaining eight are positive versions of zero-capable alpha1,alpha2,sigma1,sigma2,tau1,tau2,rho1,rho2.

Impose these fifteen polynomial equations:

(1) x^2=1+(a^2-1)y^2
(2) u^2=1+(a^2-1)v^2
(3) s^2=1+(beta^2-1)t^2
(4) beta=1+4y q_b
(5) beta+u alpha1=a+u alpha2
(6) v=y^2 q_v
(7) s+u sigma1=x+u sigma2
(8) t+4y tau1=k+4y tau2
(9) y=k+delta_yk
(10) w=b+delta_wb
(11) w=k+delta_wk
(12) T=m+S
(13) a^2=1+((w+1)^2-1)(wg)^2
(14) 2ab=T+(b^2+1)
(15) x+T rho1=y(a-b)+m+T rho2

All domains are explicit: a,beta>=2; w,T,g,x,y,u,v,s,t,q_b,q_v,S>0; the three deltas and eight quotient variables are >=0. Equations (5),(7),(8),(15) are unrestricted integer congruences represented by differences of two nonnegative quotients. Hence no sign assumption has been silently imposed on a congruence quotient.

### Power-macro soundness

Equations (1)--(9) are exactly the positive-index, nonzero branch of the cited indexed-Pell characterization. The omitted zero branch would have y=0 and is impossible because y>=k>=1. Thus (x,y)=(X_k(a),Y_k(a)).

The source power theorem uses natural subtraction a-b, whereas the arithmetic DAG uses ordinary integer subtraction. The following proves they agree, without an unpaid bound. Equation (13), with w>=b>=2 and g>=1, gives a^2>=1+((w+1)^2-1)w^2>w^2. Since a,w are positive, a>w>=b. So a-b>=0. This elementary inequality suffices; no additional Pell index argument is needed for this domain issue.

Equations (10)--(15) now meet the source power theorem's hypotheses: w>=b,k; T=2ab-b^2-1; m<T; the required growth Pell equation; and x congruent y(a-b)+m modulo T. The theorem gives m=b^k. Cancelling b>0 from m=b*output and k=e+1 proves output=b^e.

### Power-macro completeness and strengthened positive domains

For a valid power, the cited theorem chooses w=max(b,k), a=X_w(w+1), and g=Y_w(w+1)/w. These values have a>=2,g>0. It then takes x=X_k(a),y=Y_k(a). Its indexed-Pell construction chooses a larger index for u,v and a CRT-compatible beta>=2, followed by s=X_k(beta),t=Y_k(beta). Because k>=1, all x,y,u,v,s,t are positive. The relation beta=1 modulo4y implies q_b=(beta-1)/(4y)>=1, and v>0 with y^2 dividingv gives q_v>=1. The strict bound m<T gives S>=1. All other inequalities give nonnegative gaps, and every congruence can be expressed with a pair of nonnegative quotients. Thus the positive-domain specialization loses no valid power.

The inherited constructive Pell theorems are the only substantial external mathematics dependency in this polynomial elimination. The binomial packing and all raw-loader conventions are proved above.

## 6. Exact arithmetic ledgers

The own Python DAG builder emits each arithmetic gate and equality, with no simplifier and no upstream execution. Its fixed EXP macro uses31 M+39 A=70 operations,25 positive witnesses,15 equations. The seven calls in each recoder contribute217 M+273 A=490 operations,175 positive witnesses,105 equations.

The forward recoder's remaining part uses7 M+27 A=34 operations,21 positive witnesses,9 equations. Total:224 M+300 A=524 operations,196 positive witnesses,114 equations.

The reverse recoder uses three additional multiplications, so its total is227 M+300 A=527 operations,196 positive witnesses,114 equations.

The pair assembly adds3 M+1 A=4 operations. This yields the interfaces and counts in section4. There are no coefficients depending on word length and no length-indexed families of gates.

The only fixed small numerals in the emitted raw-recoder DAG are1,2,4. If only literal1 andliteral3 are free, construct2=1+1 and4=3+1 once and share them across the entire pair module. The additional cost is exactly2 A; all uses of2 and4 then alias those nodes. The raw recoder requires no gigantic fixed coefficient at all. Gigantic coefficients or literal chains for periodic tiles belong to the separate board wrapper.

These are costs for a conjunction of polynomial equations. If a single polynomial is required, residual formation and sum-of-squares combination are extra paid work. For Eeq already asserted equalities, a naive general bound is Eeq subtractions, Eeq squares, andEeq-1 additions, namely3Eeq-1 further operations; sharing or equality to zero can reduce this, but no such reduction is claimed here.

## 7. Finite validation and limitations

Own checker dilation_check.py rebuilds the six DAGs and exact receipt in memory. By default it read-only verifies final-evidence/ beside the script; --verify-dir DIRECTORY checks another existing directory. --output-dir NEW_DIRECTORY writes a new evidence directory and refuses any existing destination. Finite checks use explicit guarded raises and run unchanged under python -O. Each DAG additionally records its output expression aliases. The authoritative emitted artifacts are final-evidence/{exp,forward,reverse,pair,pair_inline,pair_positive}-dag.json and final-evidence/check_receipt.json; earlier root-level DAG files are pre-freeze development artifacts and are not authoritative. It runs1016 exact raw-word/radix residue cases,38 full binomial-extraction cases,5766 exact pair-assembly cases, and2 independently constructed tiny Pell examples. Deterministic B=2^(CP+2) is generally enormous; the broader residue checks use smaller powers of two satisfying the same proved margins. The proof, not those finite cases, supplies the universal result.

The polynomial power macro is covered by the cited constructive theorem. Finite tests cannot establish that every spurious power output is excluded. They are regression checks on arithmetic identities and orientation; the exact symbolic equations and theorem specialization supply soundness. No claim is made of witness uniqueness, practical numerical feasibility at ant scale, a new minimal operation count, or complete re-proof of the source Pell theorem.
