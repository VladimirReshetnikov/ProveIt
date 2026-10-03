# Independent release-level audit of the literal reversible source

Date: 3 October 2026. Verdict: **PASS for the pinned literal machine and the explicitly promised clean-loader family**, subject to the stated inherited primary-TM/compiler theorems. This is a mathematical proof review with replayable independent checks, not proof-assistant verification.

## What was established

- The literal source has 122,622 controls, 141,561 branches, class cut J=0, 66,066 moving branches and 75,495 zero-update branches. Its SHA-256 is `38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`.
- Independently derived symbolic product masks for every two-counter primitive prove determinism and image disjointness on **all natural counter pairs**. The masks denote the infinite sets {0} and positive integers; this is not extrapolation from testing counters 0 and 1. The saved-row serialization is independently reconstructed and checked against these primitives.
- START has no incoming row and HALT no outgoing row in every stage after fresh-start insertion. The old irreversible `init_clear_T` is not claimed to be predecessor-free. Intermediate history/prime controls are disjoint from their respective source-boundary sets.
- Whole-table regeneration reproduces every byte of the seven generated JSON artifacts. Every underlying primary TM table/interface file compared with the prior literal frontend is byte-identical. The copied `reversible_binary.py` is byte-identical to the prior Report 15 release implementation.
- All eight substantive bundled checkers pass in normal Python and `python -O`. Controlled corruption of the final serialization, a prime-arithmetic primitive, the TM table, the virtual three-counter table a prime certificate, and an invalid source guard presented to the class-count helper are rejected by the relevant checker in **both modes**.
- The loader enforces exact natural integers, binary strings, a positive cofactor coprime to 2310, START, a zero physical auxiliary counter, and exclusion of initial factors 7 and 11. A supplied ledger override is rejected. Exact source bytes are pinned before target constants are derived. Mutating returned coordinate lists or ledger dictionaries cannot alter subsequent results, and caller input dictionaries are not modified.
- Separate tests reject malformed structure/types, duplicate JSON keys, nonnatural updates, overlapping source domains and target images, and incoming START/outgoing HALT. Builder dependency tampering and loader source tampering are rejected.

## All-input composition review

The clean initial domain is

`(START, C * 2^L * 3^R * 5^T, 0)`, with L,R,T natural, C positive and gcd(C,2310)=1.

Equivalently, a validated positive initial first counter has no prime factor 7 or 11; unique factorization supplies L,R,T and the cofactor. The standard finite tape loader sets T=0 and C=1. The tape halves are nearest-head-first, the scanned symbol is 0, and the omitted tails are zero. For example left `101` and right `01` give L=5,R=2 and A=288. This interface retains the cited universal finite-input family.

The 528-instruction virtual program has only ADD and combined SUB away from HALT. Every such instruction is enabled on every natural vector. Its scratch-clear, pop, transfer, push and restore loops have the explicit decreasing ranks in PROOF.md. The cut includes scratch T=0, not just a control label. Independent execution of 2,349 small TM macro cases corroborates every one of the 29 defined transitions and its exact clock; the universal quantifier comes from the reviewed affine identities and ranks, not those finite cases.

Primitive splitting only inserts a decrement following its enabling positive test. Normalization inserts finite one-way identity chains. At a history boundary W=0; each collision macro leaves the simulated data correct, returns W=0 and changes H from h to 2h+b. Its transfer/doubling ranks force termination. At a prime boundary the encoded positive N has physical scratch zero. Multiplication, enabled division and true tests return exactly to the intended next boundary; their ranks force termination. False singleton tests and nondivisible decrements can block on malformed inputs, but cannot occur in the promised simulation. Shared destination restorers preserve the all-configuration injection property.

Consequently every enabled simulated step has a finite positive duration, no valid step can reach a false HALT, and no enabled step can run internally forever. The only clean-run outcomes are designated halting or an infinite continuation. This proves the nonblocking premise required for the periodicity corollary.

## Exact clocks and resources

The reviewed exact clocks are:

- Virtual scratch prologue: T+1 combined instructions
- TM move with movement-side value X=2Q+r and opposite value Y: 5Q+r+7Y+w+4
- Positive SUB split: 2; zero SUB or ADD: 1; fresh entry: 1
- Indegree-k normalization of incoming edge j: k-max(2,j) additional steps
- History recording: 10h+4+2b; unchanged edge: 1
- Prime identity: 1; increment: (p+7)N+3; enabled decrement: 4N+(p+3)(N/p)+3; true test: 4N+4 floor(N/p)+3
- Binary CA moving branch on pre-update selected counter c: 3+2(Z+c)+delta-4S; zero-update branch: 1

Independent literal five-counter prologue traversal plus these exact arithmetic formulas reproduces all five saved predicted-clock cases. Empty-tape initialization uses 142 five-counter steps, ends at history H=15/work W=0, and has predicted physical two-counter duration **79,936,151,060,302**. This full physical path was not executed. The T=1 example already has predicted duration 88,283,768,118,016,420,937,815,588,623,939,051,753,213; there is no efficient-conversion or uniform-slowdown claim.

The compiler constants are D=509,508, S=1,019,018, Z=20,380,380. Independent formula substitution gives **269,291,358,255** finite local involution factors, radius upper bound **3,292,955,588,459,274,804**, and observer length 1,528,527. Empty tape gives particle coordinates {-20,380,381,0,1,019,018,1,019,019,20,380,380}. No universal eager compiler object, complete gate array or CA truth table was allocated.

Independently enumerating enabled J=0 product cells gives B=350,054, r=411,291, P=199,004. Under the existing Report 15 residual formulas, the core has 761,347H variables and 700,112H+1 squares; the paid orthant version has 700,113H+1 squares. The raw residual monomial-slot bound is 3,060,678H+2. The optional clock contributes one variable and one square. These are formula substitutions, not a materialized universal polynomial.

## Periodicity and inherited lower bound

On the clean computable loader family, nonhalting implies an infinite admissible source/CA micro-path. Partial injection and a predecessor-free START imply that this forward path has no repeated node. A finite halting path of Theta CA microedges therefore yields a least reflected period exactly 2Theta+2; an infinite path gives no positive return. Theta uses the **base source's CA constants**, not the enlarged clean-target wrapper's constants or any higher-level step count.

Thus periodicity/positive return is equivalent to the designated TM halt on this family. This equivalence is not claimed for arbitrary malformed source encodings, which may block nonfinally and hence produce reflected cycles. Semidecidability on all finite five-particle configurations and the clean-input many-one reduction give the stated r.e.-completeness for the fixed CA.

The sharp lower threshold invokes Report 12's independently supplied four-mass exact-reachability theorem. The reduction is valid: positive return of x is equivalent to nonnegative-time reachability of x from F(x), which is effectively computable and preserves mass. This audit verifies the dependency hashes and implication, not a new proof of that lower theorem. Its TeX and PDF hashes are respectively `803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595` and `0d1280e962e64e8e13486aaac0fae2498ac908f37feeeffba0d682df865f3f5e`.

## Defect found and fixed before release

The original checker scripts used Python assertions. A corrupted saved serialization was correctly rejected normally but generated a PASS receipt under `python -O`. All those assertions were replaced with explicit runtime conditions/raises. This audit then reproduced both positive replays and corruption rejection in normal and optimized Python. The fix changes checker robustness, not literal source/table bytes or the mathematical construction. The added class-count helper was also hardened to pin the source and validate the J=0/guard vocabulary before deriving its counts; corrupted source guards are rejected in both modes.

## Reproduction and boundaries

`python release_audit.py /path/to/source` and `python -O release_audit.py /path/to/source` create private replay copies next to the audit script. They do not change the supplied source directory. Their receipts bind the exact audited source files and list each check and limitation. The original package's public APIs return ordinary mutable data; return-value isolation is checked rather than claiming those outputs are immutable compiler records. The unchanged compiler's immutable compiled-object interface remains its earlier audited contract; it was not instantiated on this enormous source.

The Neary–Woods universality theorem is an inherited primary dependency. The previously documented visual Table 16 review is not represented as a fresh visual transcription by this reviewer. The Morita graph construction is supported by explicitly reconstructed graphs and invariant/rank proofs rather than a claimed pixel-perfect OCR reading. No new novelty, minimum-machine-size, practical runtime or proof-assistant claim follows from this audit.
