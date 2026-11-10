AUDIT REPRODUCTION AND SOURCE IDENTITIES
======================================

The six named comparison programs are byte-exact source copies. Run
reproduce_comparators.py from any directory with Python 3.12 to reproduce
their measurements. The parent package's reproduce.py invokes this check.
The source_measure.py normalizer is unchanged from the supplied drafts.

baseline_manifest.json and metrics.json identify the larger source census.
The sources/ directory preserves the selected checker and small-source
audit inputs by SHA-256 name. The original large ZIP archives are not
duplicated here. Classifying a source as a checker is a source-role audit,
not a formal soundness proof for that program.

scan_text_corpus.py is the original audit working script. It expects the
pinned checkout at ProveIt/docs/drafts relative to its working directory.
Create an audit_work directory there before running the script. It writes
the deduplicated text corpus and its search results into audit_work/.
This is a separate source-history audit, not part of proof checking or the
offline package reproduction. The delivered text_corpus/manifest.json
records the original 320 document hashes and nested source identities.

prior_math/ contains exact selected antecedent texts with per-file nested
archive provenance. Their inclusion is attribution and evidence of prior
work; they are not presented as new results of this investigation.
