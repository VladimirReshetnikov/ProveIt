# Internal gcd and norm normalization: ROOT acceptance

27 October 2026. Accepted after complete review of the201-line main,
50-line Checks, author receipt and executed driver/freeze script, followed
by an independent fresh pair. Both compiled objects and complete logs match
the author. All eight reports contain only propext, Classical.choice and
Quot.sound. No failed author or ROOT compiler attempt was needed.

The fixed model-independent Sigma1 graph states that g divides a,b and has
a natural coefficient certificate
`g+a*u+b*v=a*w+b*z`. Its totality is proved in every internal IΣ1 model.
For nonzero a+b, the bounded positive search has witness a+b; its coefficient
witnesses remain existential. A nonzero division remainder would be a
smaller certificate, so the least certificate divides both inputs. The
zero-input case is direct. Every common divisor divides the certificate,
including divisor0; mutual divisibility proves uniqueness. Only after
this proof does Lean choice name the unique value and obtain its exact
fixed-graph instance. No Nat gcd, factorization or minimality oracle is used.

For positive R,D,f and the actual norm R²+D=D*f², the public theorem derives
positive d,s,t with D=d²*s, R=d*s*t and f²=1+s*t². The chosen gcd and its
own coefficient identity give the normalized unit certificate. Multiplying
that identity proves the cancellation used twice to derive d|g. All factor
positivity is derived. The truncated-norm adapter justifies its natural
subtraction using f>0. The caller supplies no gcd, coprimality, leastness,
Pell index or desired normalization conclusion.

Checks cover fixed graph totality, both zero-input identities, greatestness
for arbitrary divisors, coefficient-based cancellation and the literal
truncated norm. The proof is uniform over arbitrary internal values.

Independent main12.264s/Checks2.206s have peak RSS1,818,480/1,773,816KiB.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false, one thread, fresh regular
outputs and a512MiB reserve. The main log is empty. ROOT's reviewed
author-derived runner adds frozen-source and explicit object/full-log/report
comparisons; ROOT separately reviewed the complete proof and fresh outputs.

Exact reuse is86 modules, all Foundation,344 custom artifacts and37 external
boundaries with111 recorded artifacts:37 primaries and74 companions. All455
actual first artifact providers match; the complete current-header DAG and
source/object pins are checked. No dependency is refreshed. The runner's
final recheck covers1,015 distinct observed paths. Existing provenance
qualifications remain; this is not a Foundation or package rebuild.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticGcdNormalization | 488783700b1663f66b4caee71e7121eb6c50ab4efe04b39f30d63727cc6c8627 | 517c17d6efc7aa6ef20c4f269c082252daf9c77051e402ddbbf5f085cd4ea0c7 |
| ArithmeticGcdNormalizationChecks | bfbda894ceb6ce5e0a1ab459c4e7f48ed897648d47356e7efda8e37476c05067 | 893a97138e58af2d5de1d81580491f1a20f337625c91841b145646fd79d64f02 |

Accepted independent provider:
`/tmp/arithmetic-gcd-normalization-root-pnbeaddq/lib`.
The [ROOT packet](arithmetic-gcd-normalization-root-replay.json) and
[bundle manifest](arithmetic-gcd-normalization-root-replay/FILES.json)
preserve the replay, inputs, complete logs/timings and final authentication.
The separate [author packet](arithmetic-gcd-normalization-replay.json) has
its15-file manifest and original input snapshots.

The common-unit consumer, sequence composition, strong divisibility,
large-index argument, cubic congruences and complete relaxed integrality
remain open, followed by the remaining equation/PA/HA bridges. The equation
display and all coefficients and size metrics are unchanged.
