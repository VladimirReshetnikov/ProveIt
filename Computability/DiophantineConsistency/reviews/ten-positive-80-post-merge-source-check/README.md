# Post-merge 80 replay source check

At merged HEAD `e4e6227878d5fdb60106de22d5e248091e0d2ae2`, `check.py`
rechecked all 127 original source files against the frozen replay plan, all
plan and replay input hashes, and the completed replay, outer receipt and
fresh-closure result hashes. All matched. The recorded result is
`observations/attempt01.json`, SHA-256
`099bb7cad6bb9dc6d00e3851479115489416f8bf81024d757a954d5ca84d3b31`.

This establishes current byte stability of these inputs after the merge. It
does not audit every workspace change, replay Lean, bind external files, or
resolve the documented unrebuilt project/package/dynamic ancestry limits.
