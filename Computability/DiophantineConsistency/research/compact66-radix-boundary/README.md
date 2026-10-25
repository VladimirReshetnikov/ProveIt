# The present radix bound and a conditional 65-bit escape

This is a bounded, code-free ordinary investigation. It does not specify a
new accepted coefficient tuple or equation, and it does not change the
maintained compact66 page. All four coefficients would change together if
the radix changed. The accepted 295388 coefficient bytes remain the only
materialized tuple used here.

The conclusion is twofold. The existing sufficient certificates do not allow
lowering 67. A sharper cyclic-convolution estimate removes their large mass
factor and makes 65 a concrete candidate, but three controller-unit residues
and a complete replacement native-interface binding remain unverified. There
is no new calibrated endpoint, byte saving or page gain claimed below.

## 1. Exact unchanged data and the retained obstruction

Keep the exact 430 actions, 943 indexed tiles, selector indices, copy/anchor
positions, two dummy slots and all integer coefficients of the printed Phi.
Let E be its 986-position native support, including the two zero-coefficient
dummies, and put Csum=sum_(e in E)c_e. The present recipe has

    L=8807, rho=2^67, d=67L, B=rho^L, beta=B-1,
    mu=2^51-2,
    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_e c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K=DC+B*DR.

Its independently retained indexed certificate gives

    4*988*(2*Csum+6)+8 = 118788496120850159560,
    2^66 = 73786976294838206464,
    2^67 = 147573952589676412928.

Consequently 67 is the smallest power-of-two bit width satisfying that
particular conservative carry certificate. The native44 proof also retains
2*(2^65-1)+4<rho for its padding masks; this independently fails at 66 bits.
Neither inequality is proved necessary for every possible native proof.
They are sufficient premises of the currently accepted transfer, so merely
changing a numeral cannot invoke that transfer unchanged.

There is also a structural obstruction to the unchanged interface at every
even bit width b, with d=bL. Native low bits give R=3 modulo4. Whole-cell
temporal alignment with X=2^R requires R=d*w modulo dN, with no factor2 or
additive offset. If d is even this makes R even. Equivalently the existing
dummy multiplier contains rho^1063 and cannot be a unit modulo even dN.
Changing an odd padding prime cannot fix that contradiction. This is an
obstruction to transferring the unchanged native interface, not a no-zero
claim about an unverified even-radix polynomial whose carry hypotheses fail.

With the literal padding coefficients retained, their maximum is 2^65-1.
Canonical, nonoverlapping radix digits therefore require b>=65. Thus 65 is
the only lower bit width left by these two particular layout requirements.
Other padding layouts or other rank geometries are outside this conclusion.

## 2. A sharper coefficient bound, before decoding

The low-mask constraint on C supplies Boolean bits at ordinary supported
positions and two allowed low bits at the upper-dummy position1063. A digit
there can be3, because its low and upper dummy bits may coexist. The
origin adjustment creates its prescribed Start bit; it does not invalidate
the uniform bound. Hence every rho-digit of the supported cyclic word C is
at most3. Canonical words with only the independently chosen safe low-dummy
bits have every digit at most1.

Regard these words first as formal cyclic coefficient arrays modulo
x^(LN)-1. No assumption that a selected cell is already a valid tile is
used. The nonnegative convolution kernel DC+x^L*DR has coefficient sum

    A=2*Csum+5.

For each output position its convolution coefficient is a sum of kernel
coefficients times digits at most3. Therefore it is at most3A. This is a
coefficientwise bound, not the product of two full coefficient sums. It
holds for arbitrary supported cells, every number N of cells, cyclic wrap,
and simultaneous allowed dummy choices. Coincident kernel exponents simply
add into the same nonnegative sum.

Now set b=65 and rho_65=2^65 only in this mathematical estimate. Write
Hc=2*Csum+6=A+1. The old exact certificate implies

    4*988*Hc+8 < 2^67 = 4*rho_65,
    Hc < rho_65/988,       3A < rho_65/4.

For an arbitrary binary rotation of C, separate a whole-digit rotation
from an intra-digit shift epsilon with0<=epsilon<65. When epsilon<=63,
the shifted digits are at most3*2^epsilon, hence at most3*rho_65/4, and
no digit spills. When epsilon=64, the only possible spilling bit is the
allowed upper-dummy bit. Its carry is1 into the next cyclic digit; the
remaining digit is at most rho_65/2, so every resulting digit is at most
rho_65/2+1. Adding either rotated-word bound to the unrotated convolution
bound3A remains strictly below rho_65. For epsilon=0 the simpler bound3
also suffices. Thus the native sum

    (DC+B*DR)*C + binary_rotation(C)

has no radix carry at 65 bits. This explicitly handles arbitrary supported
predecoded assignments and the known upper-dummy spill. It does not infer
selector uniqueness or internal aggregate-payload carry freedom early.

For a canonical aligned word the digit bound improves to A+1=Hc for F,
because all C digits and its aligned rotate are at most1. In particular
2C+F has each formal digit at most Hc+2. Since rho_65>16 and
Hc<rho_65/988, Hc+2<(rho_65-1)/3. Summing the geometric series gives

    2C+F < q/3, q=B^N.

This supplies the actual strict raw-slack estimate used by the inherited
blank-helical positive converse. It is stronger than needed for alpha>0.
This estimate concerns the native F, not the shifted fixed MF source port.

## 3. What the fixed masks and alignment would still require

At rho_65 every Phi coefficient is still a nonnegative digit: selector
coefficients are below2^45 and control coefficients at most2^50. The
aggregate complement lemma, all copy/anchor basis identities and the two
support intersections depend on those coefficients and positions, not67.
They do not change when evaluated at another radix. The actual clean-band
and anchor argument must use the carry/spill conclusion of Section2 in
place of its coarse mass premise; no inherited assertion with a failed
hypothesis is being invoked as though unchanged.

The unchanged thirteen padding coefficients2^65-1 now occupy full65-bit
digits, but remain less than rho_65. The last coefficient is2^19-1.
Their population is still13*65+19=864. All intended aligned products have
largest unshifted position8791, while these tests occupy8792..8805. They
therefore test actual zeros in canonical words, including all safe dummy
choices. For inverse decoding the original clause/copy/anchor tests are
still present; these extra zero tests can be retained without using the
false inequality2*(rho_65-1)+4<rho_65. They are masks, not extra summands
in the convolution of Section2.

The complete formulas for MC and MF_native then have disjoint canonical
digits and give

    pc(MC)=65L-986, pc(MF_native)=986,
    MC=2 modulo4, MF_native=4 modulo8,
    0<MC,MF_native<beta, 0<DC<B.

The shifted source port would be MF_source=MF_native+beta exactly once.
These observations identify a replacement proof route; they are not an
actual65-bit finite support audit or a completed new native certificate.

## 4. The remaining concrete completeness obstruction

Changing b changes d,B,DC,K and the actual-rank controller. Use the same
proved prime lambda=581197 and k=lambda-1=581196 as a conditional template.
For b=65, d=5*13*8807. The accepted order certificates imply that2 has
order4403 modulo8807 and order581196 modulo lambda. Since65L is coprime
to these orders, the new B has those same orders. Its orders modulo5 and
13 are4 and12, respectively, and every order divides k. The existing
lambda-adic lift transfers by the elementary lifting identity, since
neither the old nor new d is divisible by lambda. Thus v_lambda(B^k-1)=1.
In particular B and B^2-1 are units at every prime divisor of d*lambda.

The bracket

    H0=1+B*DC+B^2*(DR+1)=1+B*K+B^2

must also be a unit at5,13,8807,lambda. At5 this follows without new tile
arithmetic: rho=2 modulo5, the two Laurent multipliers sum to0, K=3
modulo5 and B=3 modulo5, so H0=4 modulo5. The other three bracket residues
have not been computed or proved nonzero here. For example, at13 the
literal formula reduces to

    rho=6, B=11, K=3+4*Phi(11),
    H0=12+5*Phi(11) modulo13.

It is a unit exactly when Phi(11) is not8 modulo13. There is no justified
reason to assume this from the old67-bit residues. The8807 and lambda
brackets likewise depend on the complete indexed Phi, not just its label
set or an independently substituted port. These are precise remaining
finite obligations, not a request to generate a new tuple in this task.

If the full replacement native interface and these bracket units are
established, the existing Boolean-subset controller proof applies with the
new d. Choose fresh padded widths/heights that are powers of lambda, take
N sufficiently large, and tune the freshly encoded actual rank by the new
Gamma to R=d*w modulo dN. Odd d,N preserve R=3 modulo4 and the canonical
population phase. No old F,C,R, Gamma or private Pell tuple is reused.

## 5. Whole positive maps and claim boundary

Conditionally on that completed native theorem, soundness decodes the
new tuple's actual tiling, uses the same complete color/state conjugacy,
and obtains the original finite refutation. Completeness starts from a
refutation, constructs fresh padded native words with the new radix and
controller, and uses the uniform normalized native/Pell converse. For P66,
its existing quotient reconstruction chooses fresh

    V*=chi_S(R)/S, y*=psi_S(R),
    T*=(V*+c+R*f^2)/(c*f^2)>0.

The square-modulus identities and R=3 modulo4 phase prove integrality.
The soundness bridge is T_old=f*T. These are the same uniform arithmetic
maps, applied only after a whole coherent new native contract, never to a
mixture of old and new coefficients. The early signs Nk,Nt remain coupled
units until the retained rank proof resolves them.

The arithmetic free-port circuit would have the same66 live operations,
fifteen positive unknowns and nonzero degree157 leader once beta>0 and the
whole interface were supplied. This is a conditional syntactic statement,
not an emitted or verified new endpoint. Changing67 to65 has the same
number of printed digits; a full coefficient-size comparison would need
the fresh tuple and complete verification. No such comparison is claimed.

The ordinary native and internal-ZFC formalization boundary is unchanged.
No Lean build, application/helper/import/AST, polynomial or tuple generation,
compiler, TeX/PDF run or maintained-file edit occurred. Only source text,
existing inert data and file hashes were inspected. The separate bounded
native-premise trace by centering_api_review supplied the even-d warning
and located the retained margin/controller hypotheses; no independent
approval of this new conditional65-bit argument is presumed.
