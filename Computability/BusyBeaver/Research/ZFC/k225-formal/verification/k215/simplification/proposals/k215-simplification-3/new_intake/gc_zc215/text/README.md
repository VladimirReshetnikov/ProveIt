# Shorter proofs and GC-ZC215

21 October 2026. This packet is distinct from the earlier FT215 report.

## Results and boundaries

- Refactor the already certified K215 endpoint first. A proposed generic offset-bisimulation symmetry lemma replaces 2,240 reversed checks in 16 Lean files. Historical summed dependency compilation cost of those files was 1,118.74 seconds, 24.94% of the recorded total; this is NOT a measured new build speedup or wall time.
- The compact Rocq certificate has exactly the same decoded rows, reducing data text from 1,499,170 to 190,411 bytes. The Lean symmetry file, compact Rocq certificate and 107-line PrefixCredit.v are UNCOMPILED. No new kernel endpoint is claimed.
- GC-ZC215 combines command-tag generalization with exhaustive zero-debt enumeration. It has 215 working states and a completed ordinary mathematical consistency calibration, dependent on the explicitly included inherited numerical-calculus calibration. It is not newly certified in Lean/Rocq, and is not proved to have a shorter complete formal proof than K215.
- No 214-state construction is established. Finite failed searches are not lower bounds.
- Both newly inspected SB215 variants are defective. The separate correction archive is included. FT215 is unaffected.

## Machine conventions

hybrid215/machine.native.tm is the corrected final artifact: start 74, halt 254; SHA256 4122c18a347028ee6643428b70a8d5c81218d4937d672be3626981d7b50bf503.
The canonical table has working labels 0..214, start 0, halt 254. Its bijection is explicitly checked. A halt label is not a working state.
The raw runtime_input.reference.tm has a WRONG serializer start-0 comment and is inert historical evidence only, NOT an alternative candidate. All transition rows equal the corrected table byte for byte. The old 216 allocation is also an inert reference, not a new validated machine claim.

The direct blank-to-root check is 117,004 transitions to dispatcher 84, head -4, PC 000, logical registers [1,0,5,0,0,0,0,0,0], gap 20 and a mixed nonempty spare list. This is permitted by the universal runtime's domain. The earlier 69,143-step receipt is intermediate evidence, not the root used by calibration.

## Portable checks

Python 3 standard library only. Run from this folder using a fresh external work directory:

    python -I -B verify.py --work /tmp/proof-check
    python -I -B verify.py --work /tmp/proof-full --runtime

Never use -O or -OO. The optional runtime replay takes several minutes and checks all 6,177 guards against the exact archived census. The cheap run also checks the static conditional merge, both source operand changes, complete literal blank tape, canonical relabeling, exact certificate reconstruction and 100,000-candidate codec regression. Full runtime is an all-natural symbolic proof for primitive contracts in the owned checker, not a Lean/Rocq kernel proof of consistency calibration.

The included proof_refactor/audit_compression.py writes its regenerated certificate and metrics into its own directory. The top verifier safely runs a copy in the external work directory. prefix_credit/check_codec.py prints a finite regression receipt. hybrid215/verify_composition.py writes only the requested output path. No executable requires network access. Upstream files are data/proof references, not executed by the verifier.

## Provenance

proof_refactor/upstream contains the relevant data and recorded build logs from commit c9dc79323429112c698100f3226a6e4d56c8b782. inherited_zc contains attributed reference arguments and notices from the supplied ZC215 package. checks/ contains owned symbolic and literal runtime validators reused from the previous independently tested research infrastructure. The checks validate the stated finite/data/runtime interfaces; written logical proofs remain separately reviewable.

report.tex is the editable manuscript. Build it with a normal LaTeX distribution containing geometry, lmodern, amsmath, amssymb, booktabs, longtable and hyperref. Run pdflatex twice. No bibliography/network fetch is needed.
