Self-contained Lean source bundle

Run: python reproduce.py --lean /path/to/lean
Requires Lean 4.32.0, Python 3.9 or later, and no network or ProveIt checkout.
All eleven pinned dependencies and all three new research proof modules are rebuilt.
Source hashes are verified before compilation. Cached .olean files are not supplied.
The default compiler output directory is temporary and removed after verification.
Complete logs and verification.json are retained in verification/.

Scope: abstract enumerator equivalence for removal of the successful-MP truth
filler, cofinal parity completeness for original and modified command words, and a
complete stride-two source enumerator with arbitrary sound starting state.
No theorem here certifies a new binary transition table or a sub-252 state count.
Pinned original source: ProveIt 85633fd2f57b5dca16f87667699134d1b500ebc0.
Original attribution and proof comments remain in all source files.

Theorem endpoints
=================
All namespaces begin SetTheory.BusyBeaver.ZFC.

EnumNoFiller254.enum_halts_iff:
  Halts iff Code254.C254 Code254.F for the enumerator that omits the
  successful-MP truth filler, with the original exhaustive scheduler.
EnumNoFiller254.halts_iff_original:
  Modified Halts iff Enum254.Halts.

ParityCandidates254.Original.cofinal_uniform_parity:
  If C254 F, then for every g,B there exist a nonempty command word W and k
  with code(W) >= B, code(W) = g+2*k, and W halting from every working state.
ParityCandidates254.NoFiller.cofinal_uniform_parity:
  The identical statement for the verified no-filler command semantics.

EnumParity254.safe_start_iff (s, hs : Enum254.Inv s):
  HaltsFrom s iff C254 F, for the complete stride-two source enumerator.
  The original execAt and all original logical rows are unchanged; only
  candidate fetching increments np by two instead of one.
EnumParity254.complete_from:
  C254 F implies HaltsFrom s from every initial six-register state,
  without a soundness-invariant assumption.
EnumParity254.zero_formula_start_iff (pl,np,d):
  HaltsFrom <pl,np,0,0,d,0> iff C254 F, for arbitrary pl,np,d.
EnumParity254.halts_iff_original:
  The zero-start stride-two enumerator halts iff the original enumerator.

Verification references
=======================
manifest.json contains the topological module order, SHA-256 digest for
all fourteen .lean sources, repository pin and each vendored source path.
verification/verification.json records the final fresh-source build result,
module return codes, compilation commands and timings. Its relative log
names identify full compiler output, including the final axiom audits:
  EnumNoFiller254.log
  ParityCandidates254.log
  EnumParity254.log
Every displayed endpoint uses only propext, Classical.choice, Quot.sound.
No custom axioms, sorry, admissions or previously built .olean files are
needed. The source proofs do not include the physical LOAD contract, the
literal register-program bridge, a changed blank initializer, or a new
binary-machine Con(ZFC) endpoint. Those remain separate obligations.

Final prepared-runtime comparison
=================================
The no-filler change was additionally checked against the final two-overlay,
unit-stride 253-state runtime, using its frozen table directly. All 8,356
changed-source instruction guards and 288 exact unit-loader whole-tape cases
pass. The loader changes (g,L=0) to (g+1,L=g+1). The ordinary instruction
footprint, 53 protected register-box rows and explicit all-gap loader support
still require all 506 transition rows. No whole state or individual row is
freed; the runtime stays at 253 working states. Blank initialization remains
outside this conditional runtime comparison.

The separate check_no_filler_unit253.py accepts --runtime-root pointing to
the portable runtime reproduction bundle; --table may select its frozen
old-label table. It writes a complete, portable JSON row-footprint report.
The recorded final comparison is no_filler_unit253/results.json. This check
supersedes the earlier comparison against the 254-state stride-two runtime.
