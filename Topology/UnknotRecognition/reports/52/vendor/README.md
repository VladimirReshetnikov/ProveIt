# Unmodified upstream modules

These two files are byte-identical to the user's ProveIt repository sources at
ref `7518823550fbc8c217bc8be0113fe52002e77465`, under
`Topology/UnknotRecognition/fast/fastunknot/`.

- `interval_orbits.py`: 19,041 bytes, Git blob
  `e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8`.
- `interval_orbit_verify.py`: 12,612 bytes, Git blob
  `0ccb56a0e8b5f1255384121d7417441314727720`.

They were retrieved through the connected GitHub read interface and their exact
Git blob identities were independently recomputed in the container. No helper,
scheduler, or verifier code was modified. New code loads them separately and
checks those identities. The mathematical method and all delivered benchmarks
use the classical AHT periodic rule; the sharp rule remains present unchanged.

These pre-existing files retain their upstream authorship and licensing; the
new-files MIT-0 notice does not purport to change their licensing. The verifier's
own header identifies its report-47 MIT-0 origin. Consult the originating
repository for any additional upstream licensing requirements.
