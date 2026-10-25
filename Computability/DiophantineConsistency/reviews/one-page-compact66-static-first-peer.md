# Compact66 complete first frozen static peer review

Verdict: **CHANGES REQUIRED — proof wording and control classification**.
No implementation defect was found in the complete static review. The
coefficient-indicator proof contains a false statement at exponent 1,
and one negative control needs an explicit coverage classification.
Neither finding authorizes changing the held package or executing it.

This review binds `candidates/one-page-compact66` at HOLD SHA-256
`f2eb5a9b79a1bad4c1e77e4b96ac16b7a8707499ab6e3a2fd5d497943fe62801`
and SOURCE_PINS SHA-256
`94ac9869ab0ddf92e9b189919c02fa8e6cc1efb8479c8190c01275adc19e3f44`.
Paths below are relative to `Computability/DiophantineConsistency/`.
The author package was unchanged throughout this review.

## Findings

1. **INDICATOR_E1_PROOF, correction required.** At
   `RECIPE_PROOF.md:182–184`, immediately after defining the indicator,
   the proof says “the absence at e=1.” Every selector exponent 0 through
   942 has a positive coefficient. In particular, the accepted tile at
   index 1 is `(5,0,0,0)`, so its actual coefficient is
   `1+2^10*(2^34-5)>0` and `I_1=1`. The omission at exponent 1 belongs
   to the old MC subtraction over `E\{1}`, not to Phi or its indicator.
   Replace that sentence with an explicit statement covering both selector
   positions 0 and 1, and distinguish the subsequent MC correction.
   The displayed MC equation and the code's whole formal/raw-byte
   comparison already implement the correct identity.

2. **SET_DOMAIN_CONTROL_CLASSIFICATION, clarification required.** At
   `FRONT_AUDIT.py:292`, `j<430` becomes `j<429` under the label “set
   action range.” This rejects the declared full-430-index coverage
   contract at `RECIPE_AUDIT.py:269–270`; it is not evidence that the
   resulting mathematical set or coefficient changes. The existing
   accepted transition tiles 291 and 431 have the same right rank 150,
   and copy tiles 724/725 recover the same target 160. Thus action 429's
   set contribution already occurs at action 289. Explicitly label this
   case a coverage/schema negative in the source/control documentation,
   or use a genuinely changed-set mutation for a semantic-corruption
   claim. The stricter coverage guard itself is sound, and the separate
   complete 430-action and 943-tuple comparisons remain necessary.

No other concrete defect was identified. These are findings against the
exact frozen checkpoint, not results of a failed application run.

## Complete read and authentication

Read every line of the final wrapper (439/28105 bytes), recipe parser
(491/25951), local grouped core (748/40437), adopted arithmetic auditor
(487/26934), producer (109/5684), outside renderer (171/10026), PROOF
(203/10614), RECIPE_PROOF (268/13641), README (57/3534), DESIGN (90/5524),
TOOLCHAIN (72/4930), actual TeX (143/5244), complete map, historical DAG,
seed, fixed native reference, pins and HOLD. This includes all executed,
control, I/O and unused entry-point code, not merely the preliminary diff.

Prior complete independent reads of the unchanged ordinary/native/Pell
proofs are reused openly under fresh whole-byte authentication. They are
the fifteen66 proof, source36 ordinary and inherited P67 proofs, source51
squared-modulus proof, source54 short-composition proof, index-weight
proof, indexed943 proof, grouped ordinary recipe and binary ordinary
proposal. The compact-parameter note was also read completely here.
The JSON names and hashes each reused proof. The unchanged 748-line core
and 487-line adopted auditor were nevertheless reread completely here.

Freshly authenticated all 39 external and 19 own pins, 19 held local
payloads totaling 181120 bytes, the 3309-byte HOLD and separate 10026-byte
renderer. The candidate inventory is exactly those payloads plus HOLD;
all four source outputs and five render outputs remain absent. Every
member and exact inventory of all six closed parents authenticates:

| Parent | Payloads | Payload bytes | Manifest SHA-256 |
| --- | ---: | ---: | --- |
| `candidates/one-page-fifteen66` | 47 | 367628 | `065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424` |
| `research/grouped-fixed-coefficient-recipe` | 2 | 24747 | `f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594` |
| `research/indexed-tile-enumeration` | 38 | 359892 | `e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84` |
| `research/compact-tile-parameters` | 2 | 14125 | `5dafe5e3d18abb8d8a4e2254d7ac777d9db21933a8b768eba2c46535a9e3fdf9` |
| `research/binary-pass-cleanup-tiles` | 2 | 16766 | `80d44e88695ed56036aaeab3a50292a388bbf2cd7e960463125c7a75fb349a6c` |
| `candidates/one-page-grouped66` | 59 | 446360 | `187ce13905b346ccb435e86745b60f212dc46c9c726307e5cd82cb98b9e7c886` |

This is 150 payloads and 1229518 bytes. Inspected all existing compressed
ports and all 295388 decompressed bytes, equal to the complete accepted
ports and their canonical raw hashes: beta 73759, K0 74111, MC 73759,
MF_source 73759. No coefficient or tuple was generated.

The TeX is exactly the accepted 1425-byte arithmetic prefix followed by
the complete 3819-byte binary ordinary body. Its SHA-256 is
`dd56700d91a2805bd6051bc608522a30fb8cfdd45bbe0677de458215316d89af`;
the body's is
`86f7c12435d09e11a2df312b407da50bb833e34129582e94fdc05a638ae89698`.
The full body equals the binary proposal's entire literal block. Its
3555 nonwhite source characters, versus grouped 3970/3694 and compact
3854/3587, are source metrics only. PROOF sections 1–5 are byte-identical
to the accepted fifteen66 proof.

## Actual recipe and native semantics

All six replaced recipe fields are completely extracted, parsed, scoped
and proved before normalization: direction domain; head/set/rank;
all ten table rows and domains; payload; digit/remainder/decoder;
positional sum. Explicit lexical environments exclude self arrays,
unavailable functions, leaked row indices and shadowed sum binders.
Every expression is consumed; the fixed reference is not substituted
before those checks. Nonfield prose, punctuation, alphabet, seed and
footer still meet the entire native display-skeleton guard.

The payload collector proves the full identity in independent w,n,e,s,
then `v_new+v_old=2^41`. Head and rank are complete polynomials, with an
independent cardinality symbol whose actual set index and interval
endpoints are separately checked. Set datum/predicate identities use
independent action symbols. Flag factoring is proved in independent M,Z,
with actual mask/nibble indices retained. The ten unchanged decoder RHSs
have complete scoped AST comparisons. All 436 positional coefficients
are collected independently, and the actual ordered alphabet and every
seed character remain bound.

The independent reference inverts all 488 accepted copy rows, including
both bit cases and injective target/rank maps. It then recovers each of
430 actions from the accepted transitions. The actual fixed decoder is
evaluated in dependency order and compared against every action. No
inherited decoder, machine program or native compiler is called.

Both rank intervals and complete copy indices are disjoint; every row
index and all four coordinates are evaluated under its actual domain.
The pass row covers 432–435, cleanup 924–927, square row 934–942, and
the other literal/transition/copy/tail blocks partition 0–942. Exactly-once
coverage and whole ordered pointwise equality of all 943 accepted tuples
precede payload evaluation. The ordinary row inverses and all binary
pass/cleanup cases are correct.

The wrapper's subclass complements only actual printed payload leaves.
Canonical stored payloads and the collected Phi basis remain old V_i;
recursive dynamic dispatch applies the complement once. The full actual
Phi therefore becomes `1+2^51-2^10*V_i` for each independent selector.
Its four control groups expand to all eleven old triples and 41 control
coefficients. All five actual native RHSs remain unnormalized and have
strict inherited scopes and acyclic dependencies before collection.
Local x and global rho are distinct; self Phi/Lambda and free indices
cannot pass the visitor.

Full formal Phi/Lambda identities precede dependent expansions. The
collector checks every formal MC/MF/K coefficient, all 3297 digits,
984 nonzero positions and both dummy holes, then every canonical raw
byte of all four positive integers. The reciprocal Phi factor's minimum
exponent is 1097, preserving integrality. The MF source shift stays
exactly the inherited single beta shift. The proof typo above does not
change these implemented identities.

The arithmetic path retains all 66 literal rows, topology and complete
liveness of fifteen positive inputs/four ports. All 23 actual TeX cuts
cover every row. The cancellation-aware N1 expansion has 323 terms;
factor degrees 22,18,62,7,2,46 give degree 157. The entire output leader
and distinguished coefficient `8*beta^92` are checked. The ordinary
indexed-source interface and both positive witness maps are unchanged;
the unresolved unit signs are not prematurely assumed positive.

## Controls, glyphs and whole pipeline

Read and traced all planned controls: 24 inherited arithmetic negatives
and four valid cases; 17 native negatives, twelve specific native-context
negatives and five valid cases; four native glyph negatives; three full
front glyph negatives and two valid hyphen cases; 47 recipe negatives,
fourteen specific recipe-context negatives, eight valid recipe cases and
nine new full-native glyph negatives. Totals are 130 negatives and 19
valid cases, with the coverage qualification in finding 2. No control was
run and no successful runtime census is claimed. A supplemental independent
read-only challenger also read the whole new wrapper/parser/TeX and found
no parser, complement, scope or callback defect; that bounded challenge
does not replace this complete peer review.

The expected full native glyph stream begins with the accepted grouped
extraction, independently checked against its complete old prescription.
The complete new Phi header, whole tile section and factored F expression
replace their full predecessors. Every new set/rank subscript, domain,
coordinate, sign and parenthesis is charged, as are the unchanged 436
seed characters, 62 alphabet characters and footer. The full front is
compared with the accepted fifteen66 extraction. Saved extraction bytes,
one Letter page and retained zero-overfull logs are separate future checks.

Only whitespace, known floor font controls U+0004/U+0005 and eligible
ASCII prose line hyphens normalize. The seventeen exact prose spans
exclude math, commands, seed substrings and intentional joins. Unicode
minus and unknown glyphs remain. Shared guarded delimiter matching covers
all 27 actual math regions (nine display, seventeen inline, one align),
first display line 19, title/first-prose exclusions and the escaped-dollar
fixture. Full-front mathematical-minus/unknown-glyph controls use the
actual comparison path.

All three programs authenticate own/direct files and six whole parents
before substantive work; project imports occur only in the authenticated
auditor. Its local core and arithmetic front have explicit retargeting.
Copied original core authentication/main entry points are unused, and the
accepted calibration retains its original transitive theorem seals.
Source-only invokes no PDF process. No compiler/optimizer/producer/Lean
module is imported by the audit path.

The producer copies entire polynomial and coefficient-binding bytes,
updates only the calibration proof hash, and binds all three files plus
producer/pins in the source index. Pure checks reconstruct all four source
strings in memory. Output and receipt guards precede materialization;
receipts resolve outside the repository, reject symlink leaves/protected
targets and reject different existing contents. All ten command receipt
paths are distinct under `/tmp/compact66-`.

Scratch rendering uses exact held TeX, fixed epoch/TZ and trailer/date
settings, no shell escape and bounded pdflatex/pdfinfo/pdftotext processes.
It requires one Letter page, 9-point body/7.7-point seed and zero overfull
diagnostics. All five artifacts are compared byte-for-byte in both pure
rerenders; normalized scratch/clock headers and sorted JSON support
determinism. Explicit raises preserve checks under optimized Python.
The ten commands are build, two source audits, two build checks, render,
two full audits and two rerender checks, with stop-on-first-failure and
full external stdout/stderr retention. Runtime checks, fresh replays,
actual visual inspection and promotion remain future requirements.

Only inert text/hash/JSON and existing gzip-byte inspection were used.
No candidate import, compilation, helper/application execution, source
output, new tuple, TeX/PDF process, Lean step or typecheck occurred. Only
these two outside peer records were authored. Root must separately
authorize any repair, reseal, new full reviews and execution release.
