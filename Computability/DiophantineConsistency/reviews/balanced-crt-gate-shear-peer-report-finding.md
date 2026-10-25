# Preserve the first peer report before correcting its explanatory trace

The ordinary source note remains unchanged at manifest a016d1e1f8fe2b33437a3502a9371257b82aef1ec4d4cc17367f509a93ae62a2.
ROOT found one false explanatory calculation in the first frozen peer MD,
SHA548949dbe003ac6dae9b8beef5ac4d4f752fd4d5e7f5445473aab4fc9ecdbcdc.
Its companion JSON is a6c387f8c060bac31db2f61316c5b00e89722ea0968337271bd50fc68f8336cf.
Preserve both complete records in git before any correction.

The report says row15's linear part becomes
`-2a+8c-2u+8z27+4z30` and equals `2L15-M`. The literal old linear part is
`6a+8b+8c+2x21+8z27+4z30`. Substituting x21=u-2a-2b gives
`2a+4b+8c+2u+8z27+4z30`, which is the actual `2L15-M` in the source note.
The note's entire row15 formula is correct, as are its declared linear
forms. No source correction, new tuple or numerical endpoint is needed.

This is a finding in the review's explanatory trace, without an application
failure or a change to the reviewed ordinary proposal. Do not accept the
first report as an error-free final record. After this preservation ROOT
may separately authorize a bounded review-report correction and fresh
ordinary recheck at the same source seal. Main PDF/TeX and Lean are unchanged.
