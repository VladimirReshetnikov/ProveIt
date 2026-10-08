# Rational-continuation validation and measurements

These maintained drivers were adapted from report 22. They import the current
production `fastunknot`, resolve fixtures from this `fast/` directory, and write
only to explicit output paths. The delivered archive remains unchanged.

Run from `fast/` (absolute script paths work from elsewhere too):

```bash
python -B rational_research/audit_montesinos.py /tmp/montesinos-audit.json
python -B rational_research/audit_subtangles.py /tmp/subtangle-audit.json
python -B rational_research/verify_checkpoint_family.py /tmp/checkpoint-audit.json
python -B rational_research/verify_identity_family.py --max-m 10 --output /tmp/identity-audit.json
python -B rational_research/benchmark.py --repeats 7 --seconds 1 --max-objects 20000 --output /tmp/rational-benchmark.json
```

The arithmetic audit checks forward-matrix fractions, uncancelled determinants,
actual component counts, exact Alexander values and checked serialization on
1,200 sources. The local audit checks adversarial certificates and invariance
under relabeling, reordering, half-turns and mirrors, with known-unknot controls.
The identity audit is integer arithmetic; its topological interpretation uses
the cited gluing theorem. The checkpoint audit includes actual diagrams,
Alexander computations and small independent smoothing cubes. Finite checks
support conventions and code; they do not replace the proofs.

The benchmark compares the same source-built diagram with the arithmetic stage
disabled/enabled. It constructs fresh diagrams before each timed recognition
call. Seven baseline/new/baseline rounds retain five new-stage samples per
round; baseline after/before is a drift control, not an independent randomized
A/A experiment. Construction plus new recognition is timed separately.
Local search uses fresh bare PDs and warm template compilation caches.
Resource-limited baseline results are censored and receive no speedup ratio.
Compressed arithmetic samples never construct a PD. Source hashes and the
repository parent commit identify the measured implementation.

Current results are in `../results/rational_20261008.json`; audit evidence and
test logs are in `../../synthesis/data/rational-*`. See
[the maintained theory](../../synthesis/rational.tex) for hypotheses, bit-cost
bounds, interpretation of the gains, and all five local-search regressions.
