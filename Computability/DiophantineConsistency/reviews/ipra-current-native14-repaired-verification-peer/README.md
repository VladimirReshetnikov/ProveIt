# Independent comparison of the repaired-parent 14-variable endpoint

The comparator subprocess actually exited 0 under the durable `run.py` wrapper and printed the single clean `MATCHED_PASS 6 rows 7821 files` line. Its checker, both saved states, all 12 complete logs and receipt match the author comparison byte-for-byte; its terminal marker pins the checker/wrapper before-and-after hashes, log and receipt. The receipt SHA-256 is `45612cbeeba4644a9e7097cb73646743811cd226fe485ed46aa74920a916e257`; terminal marker SHA-256 is `07d95f45a03c3e653547818d3865c5f8869e6e82ff202bb45662b6a38442085d`.

The result is for the historical fixed-source native theory, not current workspace sources. The fixed project-origin repair passed separately; the 848 ancestor remains author-only, and package-transitive/dynamic ancestry remains inherited.
