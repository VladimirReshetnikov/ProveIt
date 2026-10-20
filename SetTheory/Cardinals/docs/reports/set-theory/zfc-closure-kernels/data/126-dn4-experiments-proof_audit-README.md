# Independent proof audit and source specialization

These supplementary artifacts contain **no accepted machine below 225 states**.
The NIP table is deliberately named `dn4_nip_REJECTED.tm`; its verifier
reconstructs the patch and proves that a required increment is lost.

## Accepted mathematical and verification results

* `AUDIT.md` records the independent full replay of the inherited K225
  construction and the exact distinction between ordinary runtime proofs and
  the inherited K230 kernel endpoint.
* `PositiveTransport.v` is an independent, closed Rocq theorem transporting
  halting and nonhalting through strictly positive finite deterministic blocks.
  Its source, reproducibility script, compile log, kernel log, and receipt are
  included. It does not instantiate a particular TM or ZFC theory.
* `portable_seed_invariant.py` is a self-contained Python checker for a finite
  abstract invariant of the unbounded nine-counter source execution from the
  calibrated seed. `dn4_seed_invariant.json` pins the DN4 source and verifies
  6162 nonempty control edges. In particular, R6 is exactly zero on entry to
  the NIP routine. The source hash is
  `172cb099fb980b6389674e99132b637116690dac2d0884e7d3e7bdd738e428d9`.
* `seed_invariant_and_nip.tex` supplies the universal ordinary proof of that
  invariant and a correct source replacement of general comparison by a
  destructive test for R5=1. Its proposed direct binary realization fails.
* `PairAdd2.v` kernel-checks `P(A,1)=P(0,A)+2` for the exact dual-Cantor
  pairing and the corresponding composition of three register contracts.
  It does not claim a new priority result or an end-to-end TM theorem.

## Replay the seed invariant

Pass the accepted DN4 source file from the main packet:

```sh
python3 -B portable_seed_invariant.py /path/to/dn4/sites225.json \
  --verify dn4_seed_invariant.json --output /tmp/dn4_seed_replay.json
```

Omitting `--verify` computes a new fixed point and then checks it. The program
uses no repository path, third-party import, network access, sampled register
bound, or time bound on the represented source computation.

## Replay the rejected NIP patch

Pass the normalized DN4 table, whose SHA-256 is
`3b958e7bc60964dbd95c0d244c3183cc91920a89ed12139cde8e973ae55754f4`:

```sh
python3 -B verify_nip_rejection.py /path/to/dn4/simplified.tm \
  --output /tmp/nip_rejection_replay.json
```

The original table increments R8 and appends the required spare after 636
transitions. The rejected patch reaches the same next clean source path
after 648 transitions with the registers and spare list unchanged.
This is a concrete counterexample to the primitive contract. The verifier
also checks a failed startup diagnostic at the inherited 409835-step point.

## Recheck the generic transport theorem

With Rocq 9.1.0 on PATH:

```sh
python3 -B check_positive_transport.py --output /tmp/positive_transport_check
```

The script accepts `--coqc` and `--coqchk` paths explicitly. The retained
verification contains two closed assumption reports and a successful
independent kernel audit. The arithmetic file can likewise be compiled with
`coqc PairAdd2.v` and checked with `coqchk -silent PairAdd2` in a scratch copy.

## Negative experiment scope

`neg_add2_summary.json` records 30 attempted direct negation compilations:
15 placements/parenthesizations on each of the original and DN4 sources.
All need 226 or 227 states and have four internal decoder conflicts. A fresh
literal symbolic runtime attempt also fails after 568 successful guarded
cases, as recorded in `neg_add2_runtime_failure.json`.

The failure concerns an old NEG decoder row also used as a helper by WIM
decoders at states 150 and 153. It is not an omitted second copy of the
negation macro. These are bounded construction experiments and counterexamples;
they establish no lower bound on possible machine encodings.

## Scanner deletion: exact rejection and conditional proof

`verify_short_scanner_rejection.py` uses the Python standard library only:

```sh
python3 -B verify_short_scanner_rejection.py \
  --baseline /path/to/original225/candidate225.klabels.tm \
  --dn4 /path/to/dn4/simplified.tm \
  --output /tmp/scanner_rejection.json
```

Both inputs are pinned by SHA256. The original source-40 counterexample
has zero logical registers and one zero spare. The old machine returns to
the correct PC after 586 transitions; the shortened scanner returns to a
different PC after 662. The complete initial and final tape supports are
recorded in `short_scanner_rejection.json`.

The same verifier checks a distinct DN4 blank-input obstruction. Old and
shortened machines reach the exact same intermediate configuration after
47000 and 46198 transitions, respectively. The tape contains seven zeros
at positions 0 through 6 between two runs of ones. The next two transitions
continue the old left scan but cause the shortened machine to dispatch at
an incorrect location. The recorded million-step diagnostic is finite;
it makes no claim about eventual nonhalting or eventual return to a seed.

`short_scanner_conditional.py` checks the complementary runtime cases. It
uses the unchanged retained induction engine from an extracted K225
archive, supplied explicitly rather than through a workspace path:

```sh
python3 -B short_scanner_conditional.py \
  /path/to/dn4/simplified_old.tm /path/to/dn4/sites225.json \
  /tmp/scanner_conditional.json \
  --proof-root /path/to/K225/portable/baseline226
```

The patch is exactly normalized `q34/0 -> 0 L q75`, followed by deletion
of q50. All 6083 guard cases whose source path contains no six-zero
substring pass, with arbitrary natural registers and spare tails.
Exactly 85 cases on 43 remaining source leaves are excluded. The complete
case certificate is `dn4_short_scanner_conditional_cases.json`. This is a
conditional local-runtime result; a new source layout and its initialization
would need new complete proofs before a 224-state claim.

## Canonical equality vacuity

`canonical_ve_k230_transport.tex` gives an ordinary consistency calibration
for replacing the full gated equality-vacuity component by its canonical
Eq-code-binder family while retaining all eight logical rows and full
membership vacuity. It combines Source 116's logical profile interpretation
with the exact current K230 core through an interpreted theorem predicate.
The actual source is invoked at the code of the translated padded matrix
before a pure logical alpha theorem changes the private bound coordinate.
This preserves actual source code/output coupling and assumes no commuting
law between the equality interpretation and syntactic renaming. The
argument was independently reviewed by the theory agent. The direct source
probe still costs 227 states, and no smaller machine is asserted here.
