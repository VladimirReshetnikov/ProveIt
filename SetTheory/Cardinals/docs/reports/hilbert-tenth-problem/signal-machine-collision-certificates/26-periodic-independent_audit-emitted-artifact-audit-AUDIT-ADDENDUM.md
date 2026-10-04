# Independent audit of the emitted ordinary quartics

4 October 2026. **PASS.** This is a separate artifact audit; it does not change the earlier proof audit, reviewed proof snapshot, arithmetic checker, receipt, or their seal.

## Inputs and execution scope

The author emitter was read in full as inert source and hashed, never imported or executed:

    /workspace/shared/substrate-semantics56-20261004/emit_sign_certificate.py
    SHA-256 51753ea012b966f3a0c16c4dbf8f9766f67bfa9c66afd56134047c469834a1bc

The following JSON files were read solely as data:

- `exports/four_signal_quartic.json`, 14,429 bytes, SHA-256 `79f81249129b5329a8cfec998363e9c69602b23b6b3f12a27284f0a4cb9237c6`
- `exports/quadratic_sign_quartic.json`, 23,241 bytes, SHA-256 `bf3c2978ab36acfc9c87327f687282e4550a214039ca20036fadf94abebd685e`

Only the freshly written independent checker in this directory was executed. It uses the standard library, parses JSON with duplicate-key rejection, validates integer coefficient and monomial types, and uses exponent vectors for independent polynomial algebra. There was no upstream/saved-code execution, physical simulation, or schedule replay. The author proof remains at SHA-256 `df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77`.

## Exact identities, stronger than finite evaluations

For each export the checker independently reconstructed all six residuals for every sign-trichotomy gadget, every Boolean-gate defining residual, and the final output-minus-one residual. The emitted residual multiset agrees exactly, coefficient by coefficient, with this reconstruction. All witness names are accounted for, with no extra or missing coordinate. The exported atoms also agree exactly with independently specified polynomials for the intended examples.

The checker then expanded the square of every emitted residual, added the results, and compared the complete exponent-vector coefficient dictionary with the exported ordinary polynomial. Equality holds exactly for both exports. Consequently the expanded polynomial equals the claimed sum of squares on **every** real, integer, or natural assignment, not just on the finite test samples.

The verified ledgers are:

- Four-signal certificate: 2 atoms, 2 logic gates, 10 natural witnesses, 15 residuals, actual degree 4, 65 nonzero monomials
- Nonsquare-spectrum diagnostic: 3 atoms, 5 logic gates, 17 natural witnesses, 24 residuals, actual degree 4, 117 nonzero monomials

Both satisfy exactly W=4A+J and R=6A+J+1. All residuals have degree at most two. Each sign gadget's zero-case slack is pinned by e_0 z=0. The complete abstract sign truth table was checked, including unrealizable combinations of atom signs: 9 cases for the first export and 27 for the second. Thus the actual gate DAG implements the displayed Boolean formula on all sign inputs.

Since an SOS vanishes exactly when every residual vanishes, the proof of canonical sign flags, canonical magnitude slack, and deterministically defined Boolean gates transfers to these literal exported polynomials. Their natural fibers are unique on accepted inputs and empty on rejected inputs. One-coordinate mutation checks are supporting regressions, not the reason uniqueness holds.

## Meaning of the two artifacts

The first export uses Q_1=d and Q_2=2y−d, with formula Q_1>0 AND Q_2>=0. On natural input d,y, this is exactly the infinite complete-macro validity set proved in Section 7 of the source. In particular d>0 and 2y>=d already imply y>0. The non-strict limiting boundary is retained. The artifact is a genuine certificate for that signal-machine example.

The second export is deliberately a recurrence diagnostic, not a claim of a signal-realizable macro. For B=[[2,−1],[−1,1]], its eigenvalues are (3±sqrt(5))/2. The first-coordinate observation starts at A=x and B_1=2x−y, so C=2B_1−3A=x−2y and

    H=5x²−C²=4(x²+xy−y²).

The exact positivity formula is x>0 AND [C>=0 OR (C<0 AND H>=0)]. These are precisely the exported atoms and logic. On the declared natural-input domain, it is equivalent to x>0 AND x²+xy−y²>=0: if C>=0, then 0<=y<=x/2, which forces the quadratic to be positive. That simplified predicate must not be silently extended to arbitrary signed y; the export explicitly declares natural inputs.

## Independent finite regressions

For each export, every natural input pair in [0,20]² was assigned its independently constructed canonical witnesses. The expanded polynomial and residual SOS agree and evaluate to 0 on accepted inputs and exactly 1 on rejected inputs:

- Four-signal artifact: 310 accepted and 131 rejected inputs; 8,020 admissible one-coordinate witness mutations rejected
- Recurrence diagnostic: 300 accepted and 141 rejected inputs; 13,168 admissible one-coordinate witness mutations rejected

There are 21,188 rejected mutations in total. An additional 100 signed off-graph assignments per artifact exercise the ordinary expanded polynomial. Counting canonical and off-graph cases gives 1,082 direct expanded-versus-SOS integer evaluations. Full details are in `receipt.json`.

## Replay and limitations

Run with Python 3 and assertions enabled:

    python check_exported_quartics.py --source-dir /workspace/shared/substrate-semantics56-20261004

The source directory can be relocated. It must contain `emit_sign_certificate.py` and the two named files under `exports/`, with the pinned bytes. The checker hashes the emitter but does not import or execute it. It reads only these three files and writes its JSON receipt to standard output.

This checker explicitly refuses `-O` and `-OO`; the refusal was tested. The previously sealed `../check_exact_algebra.py` also relies on assertions and must be run without optimization, although it does not have a fail-closed optimization guard. Preserve that restriction in release tooling. The author's emitter uses explicit runtime checks rather than assertions, but it was not run as part of this audit.

This audit certifies the two supplied polynomial artifacts and their exact relation to the proved sign construction. It does not claim a completed parser from arbitrary signal machines and collision macros, exhaustive testing of an untrusted general compiler interface, or proof-assistant verification. No substantive artifact correction is required.
