# Evidence-freeze history

The first presentation-only freeze attempt refused before creating `inputs/`.
Its generic source-archive comparison expected the predecessor release manifest's
on-disk mode (0444) to equal its ZIP entry mode (0644). That predecessor manifest
intentionally excludes its own metadata; its archive normalizes the self-entry
to 0644. The owned freeze code was corrected to check that documented exception
explicitly. No predecessor file, archive or metadata was altered or restored.

The next freeze authenticated both new source/audit packets, their archives, and
the predecessor's manifest/archive. It copied 213 files with content, modes and
nanosecond mtimes preserved. Fresh inventories matched before and after over
355 original objects. The historical 333-object audit boundary was checked
against current original bytes and metadata; a subsequent explicit directory-set
check and containment check for the historical 51-object source scope also
passed. The final `freeze_inputs.py verify-originals` requires these stronger
checks. The final freeze tool SHA-256 is recorded by final release verification.

The first fresh snapshot was taken after initial inert inspection and before
copying. Access times are intentionally excluded. This is a scoped observation,
not a retroactive assertion that every unrelated historical workspace object
never changed. Existing historical narratives, including the predecessor's
Report69/70 change qualifications, were retained unchanged.

The first locked article replay produced the exact expected PDF, but correctly
refused to report PASS because this new QA history file was added to the release
while that build was running. Its failure record remains externally retained in
`/workspace/shared/oeis-uniform-locked-v1-20261004`. No frozen input or predecessor
was changed. The locked replay was restarted from a fresh output directory after
the QA write, with all release writes paused for the full build interval.
