# Appending a zero-valued spare

**This is an interpreter experiment with a rejected blank initialization. It is not an additional ZFC-consistency candidate.**

The native table differs from the pinned primary K215 only at row `198/0`: replace `1 L 40` by `0 L 40`. For the unchanged primary source, the inherited symbolic checker successfully derives all 6,176 primitive cases with its increment contract parameter `append=0`. Increment therefore appends a spare of value zero instead of one; the other source effects are unchanged. The actual complete case records are included, compressed, along with the successful original run log.

The blank start reaches state 35 at head 4 after 78 transitions with one-cells exactly `[-3,-2,2]`. Row `35/0 = 1 R 35` then moves forever into the all-zero right exterior. This is a direct infinite-ray proof, unrelated to ZFC consistency; the intended calibrated root is never reached on this path.

`all-starts-result.json` records a search through all 215 existing initial states, capped at 300,000 transitions per state: 213 exact outward rays and two bounded unresolved runs (starts 64 and 74). `bootstrap-search.json` records a further bounded one-extra-row search: 30,960 specifications, 91 passing two finite engine fixtures, no clean root seed. These are bounded negative results, not impossibility theorems. Their historical scripts are included for the precise experiment definition; they retain original research paths and are not the portable entry point.

## Portable checks

From the packet root, using a fresh output directory:

```bash
python3 -B research/spares/verify.py --output /tmp/spares-finite-new
python3 -B research/spares/verify.py --runtime --output /tmp/spares-runtime-new
```

The default checks the literal one-row patch, replays every step of the saved blank trace, proves its outward-ray endpoint, and audits saved runtime case order and positive clocks. `--runtime` also freshly derives all append-zero contracts and checks their equality to the saved records. The original full derivation completed in approximately 162 seconds in the research environment. The script needs only Python's standard library and the included unchanged runtime helpers. The default packaging verification is recorded in `verification.json`.

The whole-tape quantified contracts are ordinary executable mathematical induction evidence, not a proof-assistant kernel theorem. A correct interpreter contract alone is insufficient to establish a blank consistency machine; this experiment demonstrates why the separate startup obligation is essential.
