# Reciprocal-note review at 1fdcaf5a6

One concrete editorial omission was found. The new CDC/GTS summaries recognize their common containment lemma but omit their common POWER theorem when making exhaustive claims. The underlying displayed equation systems and stated compiler-resource distinctions are consistent in the spans checked.

This review is immutable at commit `1fdcaf5a6589163ef1003ca676e39242edfa2619`; its immediate parent and all before/after Git blob identities are recorded in `/tmp/review_reciprocal_1fdcaf5a6.json`. All 13 changed text diffs were read completely: six articles, their six README guides, and the series-and-transseries guide, totaling 406 raw-diff lines. All 19 changed files, including six PDFs, have before/after byte counts, SHA-256 hashes and Git object IDs; all raw diffs are pinned. No PDF was rendered and no build was executed. The applicable `Analysis/Transseries/AGENTS.md` was read.

## Concrete correction

These statements at the reviewed revision undercount the shared results:

- `canonical-diophantine-certificates/article.tex:33646`: “No other theorem is shared.”
- `group-theoretic-substrates/README.md:1037–1041`: “No theorem is shared except the containment lemma”.
- `group-theoretic-substrates/article.tex:377`: “No theorem is shared”, followed by an exception only for the containment lemma.
- The same article at line 380: “Part VI re-proves one result of a neighbouring report”, naming POWER alone, with the other re-proofs assigned to research-programme notes.

There are at least two distinct common statements in the inspected Parts: the POWER macro and the binary-containment lemma. CDC lines 33511–33584 and GTS lines 5340–5394 give the same POWER contract for base at least two, natural exponent and positive output, the same fifteen equations, and the same constructive Pell dependency. Their witness conventions agree: 25 internal positive coordinates, or 26 including the output. Their displayed arithmetic charge is 70 operations. A fresh literal comparison matches all 15 equations after the explicit renaming of the base, Pell coordinates and gap variables and removal of TeX labels, alignment and whitespace. This authenticates the stated equation identity; it does not newly certify the external Pell theorem or emitted DAGs.

CDC lines 33604–33642 and GTS lines 5396–5424 separately give the same containment contract, using three POWER calls and strict digit/remainder bounds. The substitutions are `R_s→L`, `Y_s→Y`, `Z_s→Z`, `V→X`, `j→o`, `r→r_0`, `g_c→s_c`, `g_r→s_r`. Both proofs use carry-free binomial digits and oddness modulo two. PTR's new note at lines 2561–2562 explicitly confirms that both Parts re-prove its POWER macro. Thus the omission is internal to the reciprocal-note comparison, not a dispute over a new mathematical theorem.

A minimal correction should say that the identified shared results **include** POWER and containment, and remove the stale one-result tally. This bounded review does not prove that these are the only shared statements across the full reports. The original incorrect exhaustive wording is retained above as a finding record; corrections need not erase its provenance. No repository edit was made by this reviewer.

## Checked interfaces

The changed fixed-universal-polynomials note keeps the needed boundary: CDC's degree-18 raw-sandpile polynomials have 3,865/3,262 positive witnesses and 17,275/14,571 gates, but their stated r.e.-completeness uses imported physical simulations and outside computable input reductions. The inspected corollaries remain conditional; a paid arithmetic ordinary-input universal compiler does not follow. No change to the 84-operation claim follows from these reciprocal notes. The counts were compared with the published ledgers, not recomputed from archived programs.

The PTR/GTS/SMC notes correctly distinguish 25 internal POWER witnesses from 26 including the output, and the 1,475 expansions/184,016-gate source belong to Report 55's fixed-context matrix certificate. The 22/16/14/13/12-leaf alternatives count outputs as leaves, exclude the supplied index and any variable-base input, and are not gate-minimum claims. No new generic-versus-fixture equivalence was proved in this review.

The FPA note points to the prospective-isolation interface actually printed in SMC: raw keys, prospective preservation, isolation distance `2(b+r)`, and one-block radius `3(b+r)`, applied there to a rule whose forward and inverse radii are at most 90. Both compared key conventions exclude endpoint orientation. The source statements preserve full-shift and arbitrary malformed-input claims; this review does not recertify the entire four-particle timing construction or global rule table.

The clipping-table note resolves the now-published SMC locations for the fixed finite-table zero-versus-one positive-witness classification and its fixed-dimensional extension. It retains the single-polynomial, unrestricted-degree, table-dependent-coefficient scope. The transseries guide's method pointer resolves to the fixed-order connected-graph expansion, local residual/slope inverse certificate, exact-sequence-range inverse and staircase/separation statements. Exact-range rounding differs from arbitrary-target threshold recovery, and the clipping report explicitly distinguishes its floor-type threshold from the canonical ceiling-type staircase. No uniform growing-order asymptotic theorem or unbounded fixed-polynomial compiler is inferred from these pointers.

## Byte and read evidence

The JSON records 27 exact supplementary read spans, including the instruction file, and all 24 new named cross-reference targets resolve uniquely at this immutable revision. Those target spans are the extent of the extra human reading; the full unchanged manuscripts were not reread.

All literal article labels and bibliography key sequences are unchanged, in order:

| Article | Labels | Bibliography keys |
| --- | ---: | ---: |
| A196460 clipping tables | 135 | 15 |
| Canonical Diophantine certificates | 1,924 | 120 |
| Five-particle binary automata | 401 | 36 |
| Fixed universal polynomials | 732 | 86 |
| Group-theoretic substrates | 463 | 63 |
| Periodic turmite first revisits | 266 | 33 |

The fresh helper `/tmp/collect_reciprocal_review_1fdcaf5a6.py` only reads immutable Git text/blob data and writes this metadata under `/tmp`. No supplied, archived, frozen or copied predecessor program was executed or imported. Published PDF page counts, build logs, rendered theorem numbering and visual inspections remain the publisher's recorded results. External literature/Pell/simulation claims and complete arithmetic-source proofs were not newly certified. Apart from the exhaustive shared-results wording identified above, no further concrete defect was found in the exact reviewed diff and interface spans.
