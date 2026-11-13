# Independent source and checker audit

The comparison is pinned to ProveIt commit `1156099ffe30f7497d2c11ab20271f46cffcd115`. All 3,022 Python source entries in the ConciseIPRA subtree were matched to their Git blob identifiers, and all 16 incoming ZIP archives were read from their exact pinned blobs. This verifies source provenance and measurements; it does not assert that every archived program is sound. Deliberately rejected programs, packed decoders, test harnesses, source generators, and non-standalone fragments are excluded from the meaningful frontier.

## Measured result

For whole-file JSON input the empirical coordinatewise envelope moves from **245 tokens / 263 AST nodes / 462 bytes** to **244 / 261 / 461**. Allowing the existing JSONL profiles, it moves from **240 / 259 / 462** to **239 / 257 / 461**. Different programs attain the three minima. No single delivered checker is below all three coordinates of the old envelope.

| Program | Tokens | AST nodes | Normalized bytes | gzip -9 bytes |
|---|---:|---:|---:|---:|
| `checker_ast257.py` | 246 | 257 | 593 | 348 |
| `checker_ast261.py` | 252 | 261 | 593 | 356 |
| `checker_bytes461.py` | 267 | 298 | 461 | 313 |
| `checker_tokens239.py` | 239 | 261 | 553 | 332 |
| `checker_tokens244.py` | 244 | 269 | 547 | 338 |

Normalization is CPython 3.12.14 `ast.unparse(ast.parse(source))` followed by one line feed. Gzip uses compression level 9 and timestamp 0. These are finite-corpus minima, not theoretical lower bounds on possible presentations.

## Universal operational arguments

**Conditional selector.** In the original return-reservation checker, every successful call `c(g,s)` returns `None` after performing its changes to the global floor. Therefore `c(g,s) or k * bool(s or len(a) == 2)` and `k if c(g,s) or s or len(a) == 2 else 0` perform the same recursive call first, inspect the same fields in the same order, and then supply the same integer image, either the updated floor or zero. The first argument of the enclosing opener is unchanged, so the important validation of the witness before the major proof remains in place. This handles both false values `0` and `[]` correctly; it does not add progress introduction for compound formulas.

**Pattern and initialization.** Moving the assignment `k = 0` into the default expression `d=(k := 0)` executes the assignment once when the function is defined and retains the exact same default depth 0. No intervening operation observes the initial floor. For a three-element packet, the sequence pattern binds the same values as tuple unpacking. On a malformed packet, a fresh recursive frame has no bound `s`; the terminal expression evaluates its computation alternative and necessarily references `s` before accepting. Thus both versions reject, although their exception classes can differ. No branch can reuse bindings from an earlier packet.

**Four-field packet rotation.** Rotate each packet `[m,s,u,t]` to `[s,u,t,m]`, retaining the public root header unchanged. Then `r[:3]` is exactly `[s,u,t]` and `r[:2]` is exactly `[s,u]`. All other expressions and their order remain unchanged. No operation mutates these input arrays. This gives an exact correspondence of every run on four-field integer/list packets, including false and malformed fields. Unused prefix records remain unused. In particular, the remainder selector and all scope checks are unchanged.

**Whole JSON companions.** A sequence whose first JSONL record is the goal is represented by the reverse list of parsed records. Popping from the list supplies precisely the same goal and packet sequence. This is a certificate-format correspondence, not an assertion that arbitrary trailing text is accepted by both parsers. Public conclusions are unchanged.

## Verification

The final five files passed **560 isolated checker executions**, organized as **280 paired comparisons**, in normal Python and under `-O`. The two JSONL profiles additionally passed **56 comparisons of record consumption, unused records, final floor, acceptance, and success output**, with rejection exception classes permitted to differ. Fixtures cover iterator computations, equality transport, zero-source recovery, compound introduction and elimination, induction that uses its progressive hypothesis, false equations, empty sources, empty matrices, closure matrices of arity 3, malformed packets, missing packets, and attempted future-variable capture. There were no mismatches. The byte profile's normalized AST is absent from all pinned Python files and incoming archives.

The portable verifier is `tools/verify_profiles.py`. It checks the exact fixture corpus and writes `evidence/independent_validation.json`. Source members, original ZIP blob identifiers, fixture transformations, and fixture hashes are recorded in `fixtures/independent/provenance.json`. The sources and SHA256 hashes are identified in `evidence/independent_audit_summary.json`.

## Scope of the result

The mathematical axiom and rule basis is unchanged. These refinements preserve the inherited public theorem set and therefore preserve whichever equiconsistency and bi-interpretation bridge has been established for that calculus. The programs retain their original raw certificate/goal contract. They are not promoted to validators of arbitrary JSON by these changes. The separate fully validated 599-byte companion is outside this independent review and must be verified against its own matched control.

The improvements are in the empirical checker-size criterion. No new arithmetic principle, absolute simplest axiomatization, representation-independent lower bound, or one-program simultaneous domination is established here.
