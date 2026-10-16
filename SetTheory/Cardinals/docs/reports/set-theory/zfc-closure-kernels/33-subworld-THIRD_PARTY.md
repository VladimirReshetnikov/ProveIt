# Attribution and scope

The report distinguishes new research contributions from attributed sources.
It does not assign a new blanket license to the selected upstream material.

- ProveIt sources are pinned to 4747142d5d15213eb711bdadfa3cc7e769fcb7a7.
  The repository's MIT No Attribution license is retained as LICENSE.proveit.
  Exact input identities are recorded in the Lean and compiler provenance JSON.
- The explicit implicational reconstruction follows public-domain Metamath
  proof tables by Larry Lesyna, Jeffrey P. Machado, and other attributed
  contributors, based on Łukasiewicz's prior result. Every transcribed theorem
  has its original source URL in the Lean/JSON artifacts.
- Andrew Wade's compiler is retained with its supplied LICENSE.wade under
  sources/proveit/lib/jeff-busy-beaver-zfc254/ZF/generator/.
- Mira-Cult's 254-state table, mira-emmy's 253-state reduction, Jeff's proof
  program and Python design tools are prior work. Their exact origins and
  the distinct license scope are documented in machine_experiments/THIRD_PARTY.md
  and UPSTREAM.json. Wade's license does not cover unrelated upstream files.
- The report cites Friedman's 1997 notes, Geschke's lecture notes, and the
  primary Metamath proof pages. The source publications themselves are linked,
  not repackaged as standalone copies.

The new theory presentation and ordinary proofs, three new Lean modules,
reference checker, and experiment scripts are identified as contributions
prepared for this report. Generated tables remain clearly labeled as derived
artifacts, and no claim of historical priority for the mathematical ideas
or a new machine-state record is made.
