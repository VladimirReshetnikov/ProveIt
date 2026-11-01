# First conservative origin-plan author run

The author preparer terminated successfully and produced the separately frozen `../ipra-frozen-repair-plan/` manifest with 185 dirty modules. Its complete output is `author.log`; the source/replay bytes used are copied into that generated plan. This is a fixed-snapshot plan, not a Lean proof or independent replay.

Post-run inspection found that 127 candidate roots were conservatively classified as unknown because their original drivers used shared frozen `sources/` directories, which the first preparer did not recognize. No unsafe reuse resulted; those roots were marked dirty. A separate successor should authenticate those exact source-packet paths, without overwriting this plan or treating the 185 count as minimal.
