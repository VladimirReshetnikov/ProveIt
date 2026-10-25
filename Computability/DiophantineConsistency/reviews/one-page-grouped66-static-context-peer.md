# Grouped66 context-revision full static peer review

Verdict: **CHANGES_REQUIRED**. The previous `NATIVE_CONTEXT` issue is resolved
by this checkpoint. One separate blocker, `HYPHEN_NORMALIZATION`, remains.
This is a complete independent static review, not an execution approval.

The immutable reviewed snapshot is commit `740597b535`, with candidate
`candidates/one-page-grouped66`, HOLD SHA-256
`a3cfa2e26ae7f46fa0454c347467abab721e688ae2c84d2590de851c85ff3b95`
and SOURCE_PINS SHA-256
`e190e97f663e2bd6adfd0271697ad4f5e5573c2c5e0090a36fb1cd041772d6eb`.
Later working-tree revisions are outside this review. All paths below are
relative to `Computability/DiophantineConsistency/`.

## Blocking finding: HYPHEN_NORMALIZATION (P2)

`FRONT_AUDIT.py:468–475` builds its purported English hyphenation word list
with `[A-Za-z]+` over the entire actual TeX. That includes math tokens such
as `ac`, command names and seed letter runs. It therefore does not enforce
the stated prose-only normalization contract in the code, pins and toolchain.

The actual front contains `D=X+ac+gamma H` in TeX, with gamma rendered as its
mathematical glyph. In a complete extracted front, replace the `ac` fragment
by `a-` followed by a newline and `c`. The source-derived word list contains
`ac`; the regular-expression replacement joins `a-\nc` to `ac`. Thus the
full-front equality at `FRONT_AUDIT.py:585` can erase this additional ASCII
mathematical hyphen/minus glyph and accept the changed stream. This is a
static consequence of the actual regex, literal source and comparison path;
no mutation, PDF subprocess or application execution was performed.

Unicode U+2212 is preserved by the present implementation. The immutable TeX
hash, actual-TeX algebra checks and pure renderer checks also constrain the
overall workflow. Those checks do not make the whole-PDF glyph comparator's
advertised normalization contract true. The four current glyph controls
exercise other corruptions and do not cover this case.

Required repair before execution:

- Use a small immutable whitelist of actual English prose words, checked to
  occur in prose, or extract exactly prose spans while excluding math,
  commands and the seed. Permit a line-end join only for those words.
- Preserve real ASCII mathematical hyphens, U+2212 and every unknown glyph.
- Add a regression through the actual complete-front comparison path that
  rejects `a-\nc` in place of mathematical `ac`, and a valid complete-front
  case accepting a genuinely hyphenated prose word.
- Freeze the complete repaired checkpoint and obtain two fresh full static
  reviews before the separate root execution-release decision.

The held printed TeX itself is correct. No second blocker was found in the
complete reviewed scope below.

## Full read and immutable authentication

Read every line of the new auditor (648), builder (106), outside renderer
(168), PROOF (217), RECIPE_PROOF (203), README (73), TOOLCHAIN (83), actual
TeX (148), map (109), complete pins and HOLD, full 3970-byte native body,
complete seed, and all 66 source rows. Read every line of the adopted
487-line accepted parent auditor, including unused branches, and reviewed
the full selected native, Pell, calibration, composition and indexed proofs.
The previously read parent auditor was reauthenticated unchanged.

The complete 16 local payloads total 110962 bytes. The separately held
renderer has 9693 bytes and SHA-256
`eb3897621f3cc14fa72bdd187c4ae9f12a6423fa6c3629a6801b4e92ada2813a`.
All 28 external and 16 own source pins were authenticated independently.
The accompanying JSON includes the exact complete pin records and raw-port
hashes; no producer-supplied receipt was used as evidence.

Authenticated every member of all three closed parent inventories:

| Parent | Payload files | Payload bytes | Manifest SHA-256 |
| --- | ---: | ---: | --- |
| `candidates/one-page-fifteen66` | 47 | 367628 | `065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424` |
| `research/grouped-fixed-coefficient-recipe` | 2 | 24747 | `f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594` |
| `research/indexed-tile-enumeration` | 38 | 359892 | `e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84` |

Inspected the complete existing gzip payloads and decompressed all four
ports with standard-library gzip only: K0 74111 bytes, MC 73759, MF_source
73759, beta 73759, totaling 295388 bytes. All compressed and raw hashes match
the closed accepted bindings and copied inputs. This inspection generated
no coefficient, tuple or application output.

The complete actual TeX consists of the accepted 1425-byte front and exact
3970-byte grouped body. That body equals both the held reference and the
complete accepted ordinary recipe block. PROOF sections 1–5 equal the
accepted parent's sections byte for byte. The arithmetic changes retain
the existing four ports; no new calibration theorem is claimed.

## Code, mathematical meaning and controls

The prior context defect is resolved statically. All five parsed RHS ASTs
are visited before formal or numerical evaluation. The acyclic dependency
order is Phi, Lambda, MC, MF, K. Phi admits only its local x and lexically
bound selector index; Lambda admits only rho and literal arithmetic. MC,
MF and K admit their declared globals and previously proved functions.
The visitor rejects free x in integer definitions, rho in Phi, self Phi or
Lambda, unbound or shadowed indices, and nonfixed bounds/exponents. Payloads
are confined to their bound selector sum. The complete actual Phi identity
and then Lambda identity are checked before dependent formal expansion.
The evaluator's shared formal generator and hardcoded established function
values are consequently sound under the checked contexts.

The parser consumes each complete actual RHS. Sparse exact Laurent
arithmetic collects every coefficient, retains 943 independent selector
symbols and compares the whole 41-coefficient control polynomial. It then
checks all 3297 digit positions, 984 nonzero positions and both dummy holes,
followed by full MC/MF/K identities and all 295388 canonical raw bytes.
The unchanged remaining body binds the literal radix, masks, tile table,
payload, decoder, seed and constructor meanings. The grouped recipe's four
polynomial groups and shared Lambda preserve the complete old identities.

The adopted auditor still validates every one of the 66 literal rows,
their original types and topology, all 15 strictly positive unknowns and
four ports, full liveness and all 23 actual free-port cuts. Whole expansion
includes the 323-term N1 cancellation. The six factor degrees remain
22, 18, 62, 7, 2 and 46, giving total degree 157. The full leader is

`-8 q0^91 h gamma i^4 (eta+zeta)^13 w^13 s^26 T^2 f^4 (w(q0-F-alpha)-z q0)`.

Its distinguished coefficient is nonzero `8 beta^92`. The literal formula
map is checked against actual parsed cuts, rather than trusted as algebra.
The inherited calibration retains its original transitive seals and both
witness maps. Parent ordinary and native proofs remain the theorem boundary.

All control sites were read and traced statically, without running them:

- 17 actual native corruptions reach parsing, complete formal identities,
  digit or raw-byte rejection; five algebraic variants preserve meaning.
- 12 actual scope corruptions must reach `NativeContextError` with the
  `NATIVE_CONTEXT: ` prefix. Generic parse/algebra failure cannot count.
- All inherited 24 negatives and four valid controls remain present.
- Four full-native-stream glyph corruptions remain present. They do not
  cover the additional complete-front hyphen case identified above.

These are planned checks, not successful execution results.

## I/O, determinism, PDF comparison and command boundary

The builder authenticates all direct/own pins and three whole parents
before producing anything. It copies the entire accepted polynomial and
coefficient-binding bytes, changes only the local proof hash in calibration,
and binds those three outputs in its new source index. It validates every
existing source output and external receipt before any write. Both check
modes regenerate all four byte strings in memory and compare complete bytes.

The renderer authenticates the immutable source closure and complete source
records first. It copies exact TeX into private scratch space, fixes epoch,
timezone and TeX environment, disables shell escape, bounds subprocesses,
checks one Letter page and zero overflow, and compares all five output files
on rerender. Existing outputs and external receipts are checked before
materialization. There is no TeX rewriting or coefficient/compiler import.

Receipt paths must resolve outside the repository and cannot replace
protected files, symlink leaves or different existing content. Stable sorted
JSON, fixed TeX dates/trailer settings and normalized scratch/log headers
support byte replay. Normal and optimized modes use explicit raises, not
assert statements.

The full PDF audit compares every front glyph with the accepted front and
the entire native suffix with exactly prescribed replacements; saved text
must equal actual extraction. It retains floor glyph checks, all table,
decoder, 436 seed, 62 alphabet and footer characters, page dimensions and
overflow checks. Its only identified defect is the overbroad hyphen join.
No rendered metric or visual success is inferred from the charged proxy.

Read all ten held commands and their ordering: build; source audits normal
and optimized; build checks normal and optimized; render; full audits normal
and optimized; rerender checks normal and optimized. The four future source
outputs and five future rendering outputs were absent at review. No command,
application module, TeX/PDF process, Lean step or new tuple generation was
run by this reviewer. Only inert reads, hashes, JSON and existing gzip-byte
inspection were used. Outside review records are the only files authored.

The checkpoint remains held. The correction needs a new frozen seal and
two fresh complete static approvals, followed by a separate explicit root
release; this changes-required record grants none.
