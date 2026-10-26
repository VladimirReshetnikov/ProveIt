# Round21 independent review: Affine Bootstraps

## Result and scope

PASS for the new ordinary arithmetic arguments and checked finite artifacts,
relative to the explicitly retained C222/ZF/ZFC and signed-Pell calibration.
This is an AI-assisted ordinary mathematical review, not external refereeing,
a new end-to-end formal-assistant build, or a proof of consistency.

Frozen input: `diophantine_zfc_round21/intake/affine/ConZFC_Affine_Bootstraps_2026-10-25`.
No input or prior-round file was edited. The 242-file manifest passed twice.

| Endpoint | Variables | Rows | Terms | Height |
|---|---:|---:|---:|---:|
| original_horizon/balanced | 239 | 175 | 5017 | 7968 |
| original_horizon/dimension | 238 | 174 | 12743 | 7968 |
| horizon8_difference_frame/balanced | 238 | 174 | 5479 | 7968 |
| horizon8_difference_frame/dimension | 237 | 173 | 14129 | 7968 |

All have exact degree four and unrestricted integer coordinates, all of which
occur. The two source-stage quartics were independently collected as well.

## Ordinary proof review

Read the full main TeX argument through soundness, completeness and source-map
boundary; FRAME_PROOF.md, AFFINE_ARGUMENT.md, LINEAR_SELECTOR_PROOF.md, the final
frame/composition reviews, and the retained factorial-free CRT argument.

1. The lcm induction is valid. For m=ceil(n/2), at most one power of each prime
lies in (m,n], so L_n/L_m is squarefree and divides binom(n,m). The same-parity
binomial sum gives binom(n,m)<=2^(n-1), yielding L_n<=4^(n-1).
2. Both selector directions are retained: each row has an isolating full prime
power, and every prime of B has a compatible row for reverse CRT. The loss
v_p(t!)-v_p((i-1)!)-v_p((t-i)!) lies in [0,floor(log_p t)] by its zero-one
Legendre summands. Thus the linear offset R=F>L_t² suffices.
3. The exact 37-atom ledger uses 33 underlying coordinates. The integer affine
majorant proves |atom|<W for W=19+sum u². It does NOT prove atom²<W. The stronger
property from other packets must not be silently imported.
4. Keeping e_t and replacing e_(F+t) by e_(F+t)-e_t is a semantic change to a
pooled congruence, not an unconditional row operation. Its reduced nonnegative
error is correctly bounded by 65W²+60<4W³<|A-1|. The unit-anchor branch is
handled separately; all abscissa and anchor ordinate errors remain present.
5. The horizon bootstrap is acyclic: d=8h+2 is nonunit before signs; its
unpooled request forces t>=0. At t=0, F=1 and y is odd, so the endpoints would
imply 1=(y+1)(u_t-u_0), impossible. Hence t>=8 and F>=10^8. The isolated t=8
selector bound is checked directly.
6. q+1=4z+2 is nonunit before q's sign is known. Numerator requests recover
representative signs and H>=2; B divides positive C+F+1, so B!=0. Self-radix
recovery gives x>=0. The final endpoint excludes x=0 while y is signed; only
then does q^(y+1) recover y>=F. Endpoint growth precedes signed first-digit
recovery, which gives B>0 and then q>0.
7. Normalized remainders are integers because their ratio divides every other
term in the defining row. Signed low-tail uniqueness uses absolute bounds and
does not prematurely assume positive q.
8. x>=900000002>2^29 suffices for local exponent 2^23. Both the report induction
and FRAME_PROOF's dyadic argument are valid; the old 2^32 shortcut is not reused.
9. The boundary y=F is excluded only after local rows are recovered: initial
accumulator zero propagates under positive-weight updates, contradicting final
one. Label factor counting and carry-free coefficient recovery follow.
10. Completeness orders choices correctly: cofinal horizon, growth register,
sufficiently divisible large odd beta multiplier, even beta code in an odd-period
CRT class, odd B and parity-adjustable representatives, then q=1 mod4. The frame
has no private Pell coordinate and is chosen before them. The ternary gap is
nonnegative because the strict budget and integrality give M²-4sum rho²>=1.

No gap was found in these new deltas. Earlier Pell/prime-power and logical
calibration facts remain explicit inherited dependencies, not newly compiled
formal results.

## Finite evidence actually rerun

* NORMAL.json and DEEP_OPTIMIZED.json: root author checker with --rebuild,
  normal and with PYTHONOPTIMIZE=1 plus -O (including subprocesses). Both check
  source/frame/maps, all six quartics, 37 regenerated JSON files byte-for-byte,
  seven exports, deliberate negative controls, and manifest integrity.
* PARENT_NORMAL.json and PARENT_DEEP_OPTIMIZED.json: full factorial-free parent
  verifier, including its own parent check, normal/deep-O; both passed.
* check_independent.py: freshly authored here, imports no producer or prior
  checker. Reconstructs every new raw-source row from pinned parent bytes, the
  complete frame and difference-error identity, all monic eliminations and
  translations, all endpoint shears/row operations, and every coefficient and
  metric of all six quartics. Horn factoring remains covered by the separately
  replayed inherited checker rather than falsely claimed as reproved here.
* INDEPENDENT_NORMAL.json and INDEPENDENT_OPTIMIZED.json: both PASS and
  byte-identical. All declared variables occur in the full expansions.

A new package must preserve its specified inherited proof closure, not only the
final equations. No PDF render or fresh TeX rebuild was performed in this
sub-audit; mathematical TeX and generated residual exports were inspected and
checked, but visual/pagination QA is outside this completed scope.

## Composition with pooled powers

Do not add savings arithmetically. This is a different factorial-free source,
with a different meaning of F and a surviving q^(t+1) request. Existing pooled225
certificates cannot be applied verbatim. Strict ranges can plausibly remove that
derived request by the cofinal finite-tree choice, but actual source and maps
must be recompiled.

The smaller frame admits a useful extension of the pooled bound. Keep the growth
request unpooled. After its independently valid horizon bootstrap, F>=10^8 and
W>=F²>=10^16. Every affine atom in the verified ledger has squared coefficient-
vector norm, including its constant, at most 68. Cauchy-Schwarz gives
L²<=68(1+sum u²)<100W. Put b=floor(W/100). Since W>=10^16,
b>=W/101>10sqrt(W), so all absolute bases, outputs and signed indices are <=b.
For r<=15 requests, canonical signed-Pell congruences and clearing by n^b give

    E=sum_i [m_i n^b-n^(b+k_i)]² <=4r b^(4b)
      <W^(4b+1)<W^W.

Here b<W, 4r<=60<W and 4b+1<W. Also

    |2An-n²-1|>=2|A|-100W-1>W^W,

because |A|>W^W>100W+1. Hence modulus divisibility forces E=0 exactly as in the
pooled proof, including unit bases. This establishes compatibility of the bound
after growth, not a literal new pooled affine equation or count. Orientation is
still established before growth and does not depend on this extension.

No repository mutation, commit, publication or external send was made.
