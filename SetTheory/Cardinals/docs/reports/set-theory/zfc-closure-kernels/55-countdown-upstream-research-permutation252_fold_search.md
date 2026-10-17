No uniform state fold survived the new permutation252 instruction diagnostics.
The complete bounded family contained 55,471 recipes. It took 47.76 seconds
and 127,868 candidate case checks. Before searching, the unchanged candidate
passed all 8,391 strict affine cases and an exact literal replay of its entire
82,552-step blank initialization. No folded table passed the runtime screen,
so no folded table received a blank-tape run.

The input is the separately frozen
`candidate-permutation252/zfc_permutation252_old.tm`, SHA256
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
The logical-to-physical register mapping is `[6,2,0,4,3,7,8,5,1]`.
Mira-Cult designed the original machine; Jeff supplied its verification;
Wade supplied the compiler framework; mira-emmy supplied the public253
reduction. The strict diagnostic executor is copied from attributed report27
into external scratch before use. Neither frozen table nor delivered source
is modified.

Each recipe deletes one working state and redirects every incoming target to
one retained working state, without changing the retained state's row choices.
The dispatcher remains old96, and all 55 protected register-support rows must
remain byte-identical. This excludes every protected row's source and target,
including old7 and old9, which are targets of protected boundary rows. The
remaining 221 deletion sources each have 251 destinations. An initial guard
caught the omitted incoming-target restriction before any candidate completed;
the recorded complete run uses the corrected family.

The earlier public253 negative search does not automatically settle this
family. The new table changes twelve selector-entry targets. In particular,
a failed fold may enter a physical skip state outside a register-file
boundary. Arbitrary physical permutations do not preserve the skip states'
literal predecessor chain in that context. The old register permutation
argument applies to the justified Box interface and does not conjugate every
malformed-context mutation trace.

The driver first records every actual table lookup in the baseline affine
traces. For a deletion it tests affected cases in increasing baseline cost.
A survivor would then receive every case with the new named physical guards
and expected single register effect. Only a full runtime survivor would enter
a literal blank simulation, looking for the same complete zero-root frame.
No recipe reached that stage in this run.

The checker uses the four attributed generic register contracts; this search
does not generate kernel proofs for altered tables. The unchanged 55 rows
preserve the supporting literal routines. Fuel exhaustion or an unsupported
symbolic rule is a diagnostic failure, not a proof of machine inequivalence
or a lower bound of252 states. Other folds that alter protected rows, dispatcher
changes, context-specific rewrites and other register permutations remain
outside the family.

Reproduce from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_fold_search.py \
  --output /tmp/permutation252-fold-results.json \
  --scratch /tmp/permutation252-fold-replay --seconds 120
```

`results/permutation252-fold-search.json` records every deletion source and its
first failing case for each destination in the declared order, aggregate
failure reasons, source hashes, bounds and the scratch journal digest. The
frozen252 candidate and its formal verification are unchanged.
