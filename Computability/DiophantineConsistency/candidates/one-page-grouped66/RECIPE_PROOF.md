# Same four complete integers, shorter printed specification

This is a representation change of the accepted complete indexed943
fifteen-positive P66 equation. The polynomial, all66 arithmetic rows,
positive domain, degree157 and all four coefficient values are unchanged.
No new tuple, source calibration or consistency assertion is proposed.
The exact selected3970-byte constant body is the fenced TeX block in the
sealed grouped-fixed-coefficient-recipe proposal; it is also copied as
fixed/native-body-reference.txt. Its SHA256 is
9fcc86a814801751b185c82b9a131f3a4571446cef33273cef4b9a9fa3358f97.

## 1. Full coefficient identity

Let rho=2^67, B=rho^8807, beta=B-1, and G_m(x)=sum_(j=0)^(m-1)x^j.
The old control table had exactly the eleven triples below, where
(b,e,m) contributes 2^b*x^e*G_m(2x). Replace that entire contribution
by the following four terms, in the displayed order:

    A1=2^10*x^1003*(x^20+2^17)*G_8(2x),
    A2=2^18*x^983*(x^30+2^17)*G_9(2x),
    A3=2^44*x^992*(x^39+2*x^30+4*x^19+8),
    A4=2^48*x^1095*(1+2*x^1100+4*x^2201).

| Term | Every distributed old triple |
|---|---|
| A1 | (10,1023,8), (27,1003,8) |
| A2 | (18,1013,9), (35,983,9) |
| A3 | (44,1031,1), (45,1022,1), (46,1011,1), (47,992,1) |
| A4 | (48,1095,1), (49,2195,1), (50,3296,1) |

For A1 the powers are1003+20=1023,1003 and coefficients2^10,2^27.
For A2 they are983+30=1013,983 and2^18,2^35. A3 distributes to
positions992+(39,30,19,0)=(1031,1022,1011,992) with powers of2
44+(0,1,2,3)=(44,45,46,47). A4 distributes to
1095+(0,1100,2201)=(1095,2195,3296) with powers48,49,50.
The seven singleton triples use G_1=1. Thus all eleven triples occur
exactly once; expanding the two geometric factors accounts for all
8+8+9+9+4+3=41 control coefficients.

Consequently the actual newly printed expression

    Phi(x)=(1+2^51)*G_943(x)
          -2^10*sum_(i=0)^942 v(t_i)*x^i+A1+A2+A3+A4

is the old Phi as an identity over Z[v_0,...,v_942][x]. This establishes
every selector coefficient and every control coefficient independently;
it does not sample a numerical argument. In particular both Phi(rho)
and Phi(1/rho) retain their exact old values.

## 2. Derive the low mask from this same polynomial

The unchanged payload definition is

    v(w,n,e,s)=w+2^8*n+2^17*e+2^25*s+127*2^34.

For the complete accepted943 tiles every label is between0 and438.
Their nonnegative payload prefix is at most
438*(1+2^8+2^17+2^25)=14754363318<2^34. Hence

    127*2^34 <= v(t_i) < 128*2^34=2^41.

Thus for all943 selector positions their actual coefficients
c_i=1+2^51-2^10*v(t_i) obey1<=c_i<=1+2^44<rho. All41 control
coefficients are positive powers of2 at most2^50<rho. They have pairwise
disjoint supports, outside0..942. Their complete support is

    {983,...,992} union {1003,...,1011}
      union {1013,...,1031} union {1095,2195,3296}.

Writing Phi(x)=sum_(e=0)^3296 c_e*x^e, every c_e lies in0..rho-1.
Its nonzero support is S=E\{1063,1064}, where the old complete set was

    E={0,...,942} union {983,...,992} union {1003,...,1011}
       union {1013,...,1031} union {1063,1064,1095,2195,3296}.

This proof may name the old set; neither E nor its union table occurs on
the proposed page. It has986 positions; S has984. In particular1 is in S,
while1063 and1064 are the only old dummy positions.

The printed arithmetic function D_b(A,k)=floor(A/b^k) mod b gives
D_rho(Phi(rho),e)=c_e by carry-free positional expansion. For every
integer0<=d<rho, floor((d+rho-1)/rho) is0 for d=0 and1 for d>0.
Therefore the fully printed finite sum

    U=sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e

is exactly sum_(e in S)rho^e. U is only a proof abbreviation. The old
MC=beta-sum_(e in E\{1})rho^e-2*rho^1063 consequently equals

    MC=beta+rho-(rho+3)*rho^1063
       -sum_(e=0)^3296
          floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

Indeed sum_(e in E\{1})rho^e=U-rho+rho^1063+rho^1064. Combining
the three rho^1063 corrections gives(rho+3)*rho^1063. This is an exact
integer equality, including both zero dummy positions and the omitted
selector1. It changes no low-mask bit, native margin or port value.

## 3. Lambda and the entire unchanged four-port tuple

Define the fixed abbreviation Lambda=rho^4393+rho^5495. Substitute it
in precisely two places: the MF term(2^51-2)*Lambda and the K term
Lambda*Phi(1/rho). Every other MF and K term is unchanged. Since the
whole Phi identity holds for every rational argument, this preserves the
entire Laurent polynomial K, including its established integer
cancellation. Beta stays B-1 and MF is still the source high mask after
exactly one beta shift, as in the accepted parent. Lambda is fully
printed and is neither an unknown nor a fifth coefficient port.

These identities preserve all four whole integers, not an isolated K.
The four canonical little-endian payloads have lengths74111,73759,73759,
73759 bytes for K0,MC,MF,beta respectively:295388 bytes altogether.
The exact copies under coefficients/ are authenticated as whole gzip
files and after decompression; the future native audit must independently
reconstruct and compare every raw byte from the actual printed formulas.
The unchanged whole indexed/native/Pell theorem and the same two positive
witness maps in PROOF.md therefore apply to the very same polynomial.

Definitions are acyclic despite forward references on the page. Rho,B,
beta,Lambda and each geometric sum are fixed arithmetic definitions.
D_b is a general arithmetic function; the literal436-digit seed and its
fixed positional sum define A. These define the430 actions, which define
the943 tiles, then v and Phi. Finally Phi(rho) defines MC; Phi(1/rho),
Lambda and the remaining fixed powers define K and MF. No step reads MC
to construct Phi. All finite indices and every quotient/remainder occur
only in constant definitions; the equation in its fifteen unknowns is
still an integer polynomial of exact degree157.

## 4. Exact future verification and page evidence

The independent auditor first authenticates all direct and own pins and
three entire closed packages: accepted fifteen66, grouped recipe proof,
and indexed enumeration. Only then may it import the accepted487-line
stdlib-only FRONT_AUDIT.py to reuse its complete23 actual free-port cuts,
full liveness, full degree157 leader and existing controls. It imports no
producer, native compiler, optimizer or Lean module. The new producer
copies the accepted polynomial/binding bytes directly and updates only
the local proof hash plus the data index; its outputs are not inputs to
the independent native algebra.

The five actual new right-hand sides are fully tokenized and consumed,
not compared only by source hashes. A separate AST visitor runs before
any formal or numerical evaluation, in the dependency order Phi,Lambda,
MC,MF,K. Phi permits local x, lexically bound i/payload and G/sum
arithmetic, with no rho,B,beta,Lambda,Phi,D or floor. Lambda permits only
rho arithmetic and cannot refer to itself. MC permits rho,B,beta and
already proved Phi with D/floor and its bound e sum. MF permits
rho,B,beta,Lambda and G; K permits those globals and already proved Phi/G.
Neither may introduce free x or unbound i/e. All powers, geometric/sum
bounds and digit indices are separately visited as literal arithmetic or
lexically bound finite indices; a sum index is bound only in its own
body, with no shadowing or leakage. Every referenced constant/function
definition must already be established. This proves the acyclic contexts
before any stored Lambda/Phi expansion or shared Laurent variable is used.

Phi is collected over all943 formal
payload variables and all41 controls. The old complete eleven-triple
formula supplies an independent coefficient comparison. The actual new
MC must collect to the full old rho polynomial; all3297 digit calls,
the984 nonzero positions and both dummy holes are checked. Lambda,MF,K
are collected entirely as Laurent polynomials, with whole coefficient
equalities before all295388 resulting raw bytes are compared. Unchanged
tile/action/decoder/seed/alphabet/footer text and native display skeleton
are checked against the exact selected complete body, with only those
five right-hand sides masked for semantic checking.

Seventeen actual native TeX corruptions, twelve context corruptions and
five valid native algebra variations call that same full native checker.
The twelve scope controls require the specific NativeContextError path:
Lambda/Phi self reference, Phi's local x replaced by rho, free x in
Lambda/MF/K, unbound i/e, a payload outside its i sum, and nonfixed sum/
geometric bounds or an x-dependent exponent. A generic parse/algebra
failure does not count as their successful rejection. The adopted24 negative
and4 valid front/source/binding/calibration/degree controls remain. Four
additional glyph corruptions call the same complete native glyph-stream
equality used for the actual PDF. No control is a claimed success at HOLD.

The complete expected native PDF stream starts with the accepted entire
extracted suffix, replaces the full old Define/E/Then/MC paragraph by the
entire new MC, replaces the full control-sum/C-table paragraph by all four
groups, replaces both old radix factors by Lambda, and includes its whole
new definition in the initial display. Every unchanged glyph,436 seed
character,62-symbol alphabet character, constructor and footer is retained.
The entire front stream is compared separately with the accepted parent.
No selected-substring acceptance substitutes for either full comparison.

Only whitespace, known floor glyph encodings U+0004/U+0005 as U+230A/
U+230B, and automatic English line hyphenation whose concatenated word
occurs in the immutable TeX source are normalized. Direct U+230A/U+230B
already have the same representation. This equates font encodings of the
same floor delimiters while preserving both delimiters and every interior
operand. A new or unknown glyph remains present and makes the full stream
comparison fail. Automatic hyphen joining is likewise limited to exact
source words; meaningful source hyphens and all mathematical minus signs
remain. No new rendering is claimed by this specification.

The earlier charged whole-text proxy saves140 visible characters, from
2553 to2413 for the complete suffix; it is not a new PDF measurement.
The exact new full TeX source is5395 bytes versus5524. Actual fit, full
new glyph extraction and readability remain future requirements: one
612x792 Letter page,9-point body,7.7-point seed, zero overfull diagnostics,
all held commands, pure rerenders and independent visual inspection.
The maintained page remains unchanged until separately reviewed results.
