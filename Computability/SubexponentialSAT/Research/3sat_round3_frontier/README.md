# A sharper combined contraction frontier for exact SAT

Read `report/report.pdf`; editable sources are in `report/`.

## Result and scope

- Generic polynomial space: normalized coefficient 63.75735555... (eventually 64), improving the compatible retuned two-stage comparison 66.12047546....
- With maximum root degree at most ceil(s^(1/12)): coefficient 23.66616881... (eventually 24).
- Optional subexponential-space cache: time 37.93010908..., space 33.62304092... (eventually 38 and 34); under the additional low-degree premise, 14.23918819... time and 12.36130146... space (eventually 14.3 and 12.4).
- Exact component improvements: sparse incremental conditional expectations and centered antipodal coefficient extraction, with fair strengthened baselines and scoped synthetic measurements.

All coefficients multiply s/sqrt(ceil(log2 s)) on the shared wire-normalized interface. They are not coefficients directly on SAT variable count n. No smaller unrestricted logarithmic order, full SAT runtime benchmark, new formalization, global schedule optimum, or numerical domination of the alternate big-O-only manuscript is claimed. The mathematical results retain the source identities and reductions.

## Frozen evidence

Arrival ProveIt commit `d098ba436b33df19365a44dd178694ff52845d19`, 27 October 2026 02:00:24 UTC. Closing canonical pin `474ddba696a5d385c091c23fb2995f69edd13e00`, 02:11:13 UTC. All eight arrivals were filed canonically with 211 byte-identical files; no mathematical source changed. The release retains selected immutable report bytes, source excerpts, hashes and acquisition ledgers, not the ZIPs themselves. The main mathematical manuscript, relevant appendices and license are under `evidence/openai/`. The separate alternate PDF is retained as source evidence only.

All incoming code was read as data and was not executed or compiled. The prior cached-score implementation is retained with a `.py.txt` suffix as inert novelty evidence. Programs outside `evidence/` are authored for this review. The report build never compiles the evidence sources.

## Replay

Requirements: Python 3 standard library, Bash, pdfLaTeX with the packages named in the report preamble, and Poppler `pdftotext`, `pdftoppm`, `pdfinfo`. Exact sealed replay uses the Debian-style Linux TeX Live paths explicitly configured in the supplied build script. No install or network access is performed.

From the unpacked release:

```
python3 scripts/verify_bundle.py /path/to/3sat_round3_frontier_20261027.zip
python3 scripts/negative_integrity_controls.py /path/to/3sat_round3_frontier_20261027.zip
python3 -O scripts/negative_integrity_controls.py /path/to/3sat_round3_frontier_20261027.zip
python3 scripts/replay_archive.py /path/to/3sat_round3_frontier_20261027.zip
```

Replay safely unpacks the sealed archive, runs all authored checks normally and with `-O`, rebuilds only the authored report, and compares text and every page's rendered pixels. Different fonts or TeX versions may alter pixels. The checks do not formally prove the source theorem or asymptotic identities.

To rebuild only the report on the matching Linux layout: `bash scripts/build_report.sh`. On another TeX distribution, enter `report/` and run `pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex` three times, with the preamble packages installed. A conventional rebuild is supported, but identical PDF bytes or rendered pixels are not promised across TeX/font versions.
To rerun component timings: `python3 research_balancing/verify_incremental.py --benchmark` and `python3 research_practical/benchmark_packet_extraction.py`. Cube-root and adverse-profile samples can be rerun with `python3 research_practical/benchmark_root_filter.py` and `python3 research_practical/benchmark_dispatch_negative.py`. Timings vary; the recorded runs are synthetic component evidence, not SAT benchmarks.
