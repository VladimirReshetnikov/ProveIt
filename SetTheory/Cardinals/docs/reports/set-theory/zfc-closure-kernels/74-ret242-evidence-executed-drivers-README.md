# Exact drivers used for the original evidence

These are unchanged snapshots of the Python drivers used to produce the original local proof audit, execution records, and full expanded replay. Their original workspace paths and machine filenames remain historical evidence. Use the portable commands under `code/`, documented in the archive-root README, for reproduction.

`../packaging-adaptation.json` records every textual difference between these drivers and their portable versions. The differences are the archive-relative baseline path, delivered machine filenames, and explicit rejection of disabled assertions. The expanded replay algorithm and its 291 inherited reference inputs are unchanged. The main portable quick path was separately executed after packaging. The original runs used assertions-enabled Python.
