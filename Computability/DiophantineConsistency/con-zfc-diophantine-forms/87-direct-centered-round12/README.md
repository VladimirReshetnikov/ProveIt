# Direct and centered Diophantine consistency equations

Round twelve, 24 October 2026. AI-assisted research prepared by dot for Vladimir Reshetnikov.

Start with report/ConZFC_Round12.pdf; its complete editable source is report/ConZFC_Round12.tex. All displayed registers are polynomial abbreviations, not extra quantified unknowns. No consistency or global-minimality claim is made.

## Main completed result

The fully expanded ordinary polynomial direct/fixed_base/equation_integer.json has 27,916 unrestricted integer variables, exact degree 4, 758,275 monomials, and maximum absolute coefficient 320307372009918. Nonexistence of its integer zeros is equivalent in ZFC to syntactic Con(ZFC), by the mathematical proof in the report and direct_audit/MATHEMATICAL_AUDIT.md. It compiles the fixed C222 proof rules directly, without K215 simulation or Jones's universal polynomial. It is an architectural completion, not a variable-count record.

The 16,036-natural-variable companion is exactly the sum of squares in direct/fixed_base/residuals_affine.json. Its expanded form is deterministically rebuilt. The integer file itself is included in full; it is not a promise that a polynomial could be generated.

## Small-equation branch

- Ten unrestricted integers: 471 operations/degree 1245324 ; 485/1179788 ; 496/1114252 ; 545/1080888. Files norm/integer10_*.json. These are degree/cost tradeoffs.
- Eleven positive integers: 113 operations, degree 211. File positive/p11_degree211.json.
- Twenty-one unrestricted integers: degree 16. File low_degree/integer21_degree16.json.
- Twelve positive integers: 100 operations, degree 70, reconstructed from an incoming prior manuscript, not a new theorem. File positive/p12_degree70.json.
- Remaining low_degree/integer*.json files are alternative or dominated charts after comparison with the later Library supplement. They are not promoted as new frontier improvements.

All actual fixed numeral bytes are supplied. Small-variable constructions retain the inherited native/compiler/Pell/K215 calibration, unlike the direct construction. Mathematical proofs, artifact replay and formal-kernel proof are separate: there is no new end-to-end Lean/Rocq certificate here.

## Replay

Validated runtime: Debian 13 Linux x86_64, Python 3.12.14, SymPy 1.14.0 and zlib 1.3.2. Exact compressed-byte regeneration is certified for this environment, not every Python 3 release; see RUNTIME.json. Other runtimes may encode the same integer with different gzip bytes. No network and no upstream code execution are needed when these dependencies are installed.

Run python3 verify.py --output replay.json. It authenticates every shipped file, creates a fresh temporary copy, runs the explicit authored-code allowlist in REPLAY.json in normal and optimized modes, then verifies exact byte regeneration of the literal equations and coefficient files. The source packet is not modified. The affine map and nonnegativity residual JSON files are intentionally regenerated rather than shipped twice; their exact hashes remain mandatory. COMPACT_STORAGE.json identifies these omissions and the deduplicated static references. The --quick option runs normal mode only. Mutation controls deliberately corrupt selected data in further temporary copies and require rejection. Failure of a finite test is meaningful; success is not a substitute for the universal proof.

To rebuild the PDF, use sh report/build.sh or ordinary pdflatex on report/ConZFC_Round12.tex. The TeX source is standalone. The PDF build requires a normal TeX installation; the script also supports the provided minimal installation without writing to the home directory.

DEPENDENCIES.md names inherited proof interfaces. NOTICE.md and LICENSE.NEW distinguish new work from unchanged inherited material. MANIFEST.json authenticates every release file other than itself. Component receipts are historical evidence; REPLAY.json and verify.py are the current runnable contract. Upstream source snapshots are inert references and may contain historical relative paths.
