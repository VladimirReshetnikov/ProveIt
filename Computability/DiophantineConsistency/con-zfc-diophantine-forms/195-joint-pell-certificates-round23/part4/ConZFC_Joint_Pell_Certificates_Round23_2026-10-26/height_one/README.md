# Round23: pruned arithmetic-DAG height-one quartics

| Endpoint | Variables | Collected monomials |
|---|---:|---:|
| minimum484 | 484 | 24,131 |
| compact485 | 485 | 23,698 |
| compact486 | 486 | 20,007 |
| compact487 | 487 | 19,748 |
| compact488 | 488 | 19,649 |
| compact489 | 489 | 17,729 |
| compact493 | 493 | 17,058 |
| compact494 | 494 | 16,557 |
| compact495 | 495 | 16,400 |
| balanced531 | 531 | 12,020 |
| balanced533 | 533 | 11,985 |
| sparse599 | 599 | 8,279 |
| sparse600 | 600 | 8,241 |
| sparser695 | 695 | 7,135 |
| sparser696 | 696 | 7,113 |

Every equation is an unrestricted-integer polynomial of exact total degree
four, constant coefficient one, and collected coefficient set {-1,+1}.
It is nonnegative on all real tuples. Through the exact pinned inherited
source calibration, ordinary ZFC proves integer unsolvability equivalent to
Con(ZFC). This transfers an inherited theorem; it is not a consistency proof.

The new arithmetic-DAG transformations fuse available constant/scale products
into source terms, delete unused constructors, inline low-use constants as
sums of earlier constants, and expand rare scales into repeated signed
monomial occurrences. These are exact triangular monic zero-set bijections.
Repeated occurrences are not claimed to be collected height one: every final
collected coefficient is separately checked. `PROOF.md` proves all maps,
including the universal source lift with its essential hub-square term.

All nine selected Round22 endpoints are dominated by at least one selected
endpoint here. No global minimum, exhaustive frontier, literature priority,
or new end-to-end formal-kernel certification is claimed. `EXPERIMENTS.json`
records the finite search and the dominated principal210 direct transfers.
The attempted unit-specialization operation had no gain and is not used.

## Reproduce and verify

Python 3.10+; standard library only:

    python verify.py --report REPLAY_BOTH.json

The default runs ordinary and optimized Python, independently reconstructs
all coefficients from square differences, checks all source and constructor
pullbacks, every occurrence/alias/graph relation, universal symbolic lift,
metrics, and literal text; rejects mutations; and byte-rebuilds all selected
outputs and parameter-matched controls. `--single` uses the current interpreter.
`--skip-rebuild` retains independent final checks but skips producer replay.
`build.py` regenerates selected endpoints and controls from fixed configuration.

`endpoints/*/polynomial.json` lists every literal coefficient (repeated
zero-based indices are powers). `polynomial.txt` is the identical complete
equation in one-based names. `CONFIG.json` pins all selected constructor,
graph, and control choices. Controls are exact Round22 endpoint copies,
except the explicitly new h28 control. Comparisons concern the complete
normalization rewrite, which includes inherited optional scale chaining,
not an isolated single-operation experiment.

`SOURCE_BINDINGS.json` pins the four inherited original sources. The complete
calibration ancestry remains the enclosing release's `inherited_round20/`
closure, including its signed and height-source proofs. This directory alone
checks the local transformations; finite arithmetic checks are not a substitute
for that inherited source theorem. `RELEASE_WHITELIST.json` alone defines the
height-one release. Exploratory scripts, trial outputs, and caches are excluded.
