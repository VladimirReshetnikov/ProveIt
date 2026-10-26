# Ordinary proof of the held2039 algorithm

This is source-only mathematical justification, not observed numeric
evidence. The accepted tile-biased family's whole theorem applies to
ANY fixed odd L>=2031, without requiring L prime or d squarefree.
Here49*2039=99911. Its sufficient premise is the existence of an odd
prime lambda>d with

    B^(lambda-1)=1 mod WHOLE d,
    gcd((B²-1)*(1+BK+B²),d*lambda)=1,
    v_lambda(B^(lambda-1)-1)=1.                     (P)

The program checks(P) directly. No factorization, group-order claim or
sufficiency of the candidate spacing is assumed. The separate2033
reduction and its rejected finite instance are not premises for2039.
Existing code was copied and read as text, never imported or called.

## 1. Exact whole table-to-coefficient correspondence

The only numeric input is the full3297-entry original admissible942
list ../parity-clause-independent/coefficients.json, raw SHA256
626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f.
The pinned complete2999 proof/table/finite certificate/BUILD_AUDIT and
ROOT acceptance explicitly establish, for every j0..941,

    old[j]=1+1024*(1+u[j]),
    u[j]=w[j]+2^8*n[j]+2^17*p[j]+2^25*s[j].

The component bit widths are8,9,8,9, totaling34. The exact admitted
index map is g(0)=0,g(j)=j+1 for1<=j<=941, omitting the forbidden
old tile1=(5,0,0,0). The retained initializer is old929/current928,
with tile(3,436,4,4).
All printed942 tiles were independently compared with that bijection;
the certificate binds the full-list hash above and action/tile/seed
hashes. This inherited table correspondence is a mathematical premise,
not code run here and not an opaque new coefficient/program index.

The hash gate precedes JSON parsing. The code checks genuine integer
entries,3297 length, all selector congruences/34-bit words, each of34
old label powers and EVERY remaining zero, including the full tail.
Consequently (old[j]-1)//1024-1 is exactly the printed u[j]. Its
complement 2^34-1-u[j] contains255-w,511-n,255-p,511-s in those lanes.

The first new route keeps low17 bits (wbar,nbar), and toggles THIRD
p bits17+i using floor((987+i+877-j)/942),i0..7, and south bits25+i
using floor((960+i+877-j)/942),i0..8. Each floor is0/1 and equals
the indicator0<=1006+j-h<=941. Bit XOR is evaluated as x+e-2xe.
The second independent route constructs a toggle mask from that direct
interval condition and XORs the whole complemented word. Equality is
required on every selector. The actual unchanged positive north/west
colors prove0<uenc<2^34; the code also checks that whole word bound.

Both produce c[j]=1+4096*(2^34-uenc[j]),0<c[j]<2^46. Old label scaling
by4 is checked against independent explicit powers at ALL four lanes:
978+i:12+i,969+i:29+i fori0..7,960+i:20+i,942+i:37+i fori0..8.
All other slots through3296 are zero. The two entire lists must agree.
The separate physical Es={0..950} union{960..985} union{1005} has978
positions, including zero-weight dummy977 and marker1005.

## 2. Complete ports and independent arithmetic

Put rho=2^49,M=2^46,d99911,B=rho^2039,beta=B-1. Dense Horner through
ALL c[0]..c[1006] gives sum c[e]rho^(1006-e). Add bare rho18 and
B*rho9 to obtain K. A second whole-integer construction uses the other
full coefficient list and sparse binary shifts49*(1006-e), plus bare18
and spatial rho2048. Every nonzero e<=985, so exponents are positive.
There is NO bare marker. The two WHOLE integers must agree.

For each tested modulus, modular Horner and independent termwise powers
are compared with reduction of the actual entire K. All three include
both bare18 and spatial B*rho9. For core=sum960..968rho^e+
sum987..994rho^e+rho1005, the remaining ports are

    MC=beta-sum_(e in Es)rho^e,
    native=4+(M-2)rho1006+core
      +(rho-1)*sum_(e=2012)^2029rho^e+(2^32-1)rho2030,
    MF_source=native+beta.

The independent mask formulas are

    MC=beta-G951(rho)-rho960G26(rho)-rho1005,
    MF_source=B+3+(M-2)rho1006+core+2^32rho2030-rho2012,
    Gm(rho)=(rho^m-1)/(rho-1).

The exact telescope preserves18*49+32=914 padding bits plus64 core
bits. Actual whole checks require pc(MC)=d-978,pc(native)=978,
MC=2mod4,native=4mod8,0<MC<beta,0<native<beta and0<DC<B. Main's
production validate_model compares complete coefficients, independently
specified physical support and EVERY whole port against these independent
routes before controller work or serialization. These same production
checks consume the actual coefficient/support/port mutants below.

## 3. Direct general-controller verification and honest rejection

Let A=(B²-1)*(1+BK+B²), computed on whole integers. First compute
gcd(A,d), and independently compute it from the three-route residues
of B,K,H=1+BK+B² modulo WHOLE d. The two gcds must agree. This establishes
the unit condition at all prime powers in d without knowing its factors.
If the gcd is not1, REJECTED_FIXED_PREMISE is the correct scientific
outcome: no lambda can repair that fixed part of(P). All ports/coefficients
and the whole-d residue/gcd record are retained, with no candidate search.

Otherwise test EXACTLY lambda=6114*k+1,k17..216, increasing, stopping
at first success. There are200 candidates, and the first is103939>d.
They are odd. The producer checks divisor2 then odd divisors through
isqrt(lambda), returning the least factor or0. The independent validator
checks EVERY integer divisor below that factor or through isqrt(lambda)
for a prime claim. Thus a claimed prime is proved by deterministic
exhaustion; no probable-prime result or shared divisor loop is trusted.

For EACH prime, explicitly compute all of:

    p_d=2^[d*(lambda-1)] mod d,
    g=gcd(A,d*lambda),
    t=2^[d*(lambda-1)] modlambda²,
    v=(t-1)/lambda.

Since lambda>d is odd prime, B is a unit modulo lambda; Fermat implies
t=1modlambda, which is separately checked. Thus0<=v<lambda, and v!=0
is EXACTLY valuation one. The independent lambda-gcd route uses B,K,H
modlambda. It equals the whole g because gcd(A,d)=1 and lambda>d is
prime, hence coprime to d. A disagreement is an execution failure.

The actual production predicate records p_d=1,g=1,v!=0 separately.
ALL three true is exactly(P); no claim that6114 is an order/lcm or
multiple of an exact order is needed. If p_d!=1, that is an ordinary
rejected candidate, NOT an exception. A prime failing units or lift is
likewise retained and skipped. Full candidate/factor/residue/check traces
are recorded. P_BIAS_CERTIFIED means an actual(P) witness was found;
REJECTED_BOUNDED_SEARCH means only these200 candidates failed, not that
no prime exists. No outcome for2039 is known in this held packet.

## 4. Controls, byte closure and scope

Seventeen negative controls run the actual production gates. Nine mutate
actual model data: three whole-list coefficients(selector0,label969,
tail3296), two physical support deletions(dummy977,marker1005) with actual
MC bit/population changes, and four whole-port mutations(K+1,beta-1,
missing MF_source beta shift,restored obsolete bare marker). Another
rejects9 as prime. Three explicitly exercise the production finite_checks
false branches(p_d0,nonunit gcd d,lift0); these are predicate-branch
controls, not fabricated numerical prime certificates. Four further
controls reject duplicate/nonfinite JSON and Boolean/float coefficients.
Five valid cases exercise a copied/reordered whole model, primes2/3/5
and validate_factor(9,3). This last case validates the explicit factor3;
it does not invoke least_factor(9). Exact reasons or false predicates
are checked.

The single executable imports only stdlib. All guards use exceptions,
not assert, and remain under -O. PINS/HOLD authenticate self/source/data
before large integers and after comparisons, including unchanged pins.
Strict JSON and exact types reject duplicates/nonfinite/bool/float as
specified; pin paths and output paths reject traversal/symlinks. The
only write mode creates absent data/ exclusively; default modes rebuild
and compare the exact six-member set and every complete byte. Whole raw
ports are minimal unsigned big-endian. A partial failure is preserved.
Normal/O and fresh same-mode captures must reproduce the complete report
and all saved bytes; this is a FUTURE verification requirement, not a run.

The unbounded accepted family still supplies count/phase/logical-label/
occupation/all-padding/subset/actual-rank/whole-d-CRT/P66 proofs. A later
finite success could discharge only its(P_bias49,2039). It grants no
Carrier65/page/circuit/format promotion or actual unsolvability/consistency
decision, global minimum, new formal-kernel/internal-ZFC replay or Lean.
Every2033 first output and frozen source remains untouched. No new code,
helper, import/AST, math application, TeX/PDF or render was executed here.

## 5. Preserved first source finding and bounded prose repair

ROOT's full source read found the copied initializer label error in
section1 before any independent2039 static review or application. ALL
seven first frozen files and the original author seal are preserved
verbatim in ../tile-biased49-length2039-controller-probe-first-frozen/,
with explicit inert PROVENANCE.json. This repair changes only that label,
the valid-control call description above and this disclosure. The
executable is byte-identical, SHA256
2c7fc5da173e91e8aa5db95bb15e5086a248f1890ccff48c2064ed70cd5a50bf.
PINS/HOLD/MANIFEST and a separate new author seal bind the repaired proof.
The three finite_checks fixtures remain explicitly predicate-branch tests,
not numerical prime certificates. ROOT is a contributor, not a peer.
