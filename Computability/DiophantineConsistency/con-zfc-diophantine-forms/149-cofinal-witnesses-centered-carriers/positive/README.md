# Ten-positive lower-Y equations

**New useful points: 79 binary operations / exact degree 382, and 80 / 338.**
Both retain ten independent strictly positive integer unknowns and the entire
indexed BFS943 radix67 fixed tuple. The largest fixed port has 592,884 bits.

| Literal DAG | Chart | Weight | Operations | Degree | Role |
|---|---|---|---:|---:|---|
| `q2_v2.json` | X=qw,Y=q²s,D=q⁵ | V² |78|516|dominated control|
| `q2_bv.json` | X=qw,Y=q²s,D=q⁵ | bV |79|382|useful tradeoff|
| `q1_v2.json` | X=q²w,Y=qs,D=q⁶ | V² |79|456|dominated control|
| `q1_bv.json` | X=q²w,Y=qs,D=q⁶ | bV |80|338|useful tradeoff|

The complete equations and both proof directions are in `PROOF.md`; the
article-ready exposition is `report_section.tex`. The coherent coefficient
payloads, printed recipe and offline reconstruction are all included.

## What changed

The newest inspected incoming Centered Residues package already gives 75/626,
76/464 and 77/460. Its arithmetic sharing is reused, not claimed as new.
Coprime Products already gives the q² partial chart at 80/382; sharing reduces
that to 79/382. The new low-Y chart changes X as well as Y, preserving the
visible q⁴ first-index modulus. It recovers the projection before the full
q⁶ denominator, then derives q=2^m and q⁶|X at zeros. Its native transport
uses Wbase=qw, not the new input w. This repairs both the old rejected chart's
index defect and the potential transport mismatch.

The signed unshift, Pell doubling, universal folding/rank/rounding and whole
native/refutation calibration are inherited and explicitly credited.
These are local improvements, not global-minimum or historical-priority claims.
The ordinary theorem is no-positive-zero iff Con(ZFC), formalizable in ZFC
at the named retained calibration. No consistency proof, zero-existence claim,
new complete proof-assistant certificate, or arbitrary-port specialization is made.

## Reproduce offline

Python 3.10+ and its standard library suffice. Run from this directory:

    python3 -B build.py --check
    python3 -B verify.py --output /tmp/positive-check.json
    python3 -B -O verify.py --output /tmp/positive-check-O.json
    python3 -B rebuild_coefficients.py

The producer reads frozen JSON only; it executes no inherited program. The
independent verifier does not import the producer. It authenticates copied
source pins, reconstructs all four fixed integers, checks every graph row via
28 symbolic cuts, proves the full leading forms, checks topology/liveness and
counts, and rejects ten actual algebraic corruptions per graph. Normal and
optimized receipts agree. The q1 leading form retains the degree tie in cT-R.

`SOURCE_PINS.json` is the active local ledger; every listed path resolves here.
`PROVENANCE.json` records archive hashes and the snapshot. Historical relative
ledgers under `provenance/` are preserved unchanged, not active path inventories.
Copied `.py` sources under provenance are static historical artifacts, never
executed or imported. The unbounded proof is not established by finite zero tests.

No remote repository was modified. New work was prepared with AI assistance;
independent review means a separate review within this workflow, not external
human endorsement. No smaller-radix specialization is asserted in this component.
