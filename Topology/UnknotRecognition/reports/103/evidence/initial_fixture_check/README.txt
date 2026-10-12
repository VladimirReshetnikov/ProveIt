Initial isolated fast-only check, superseded by ../clean_release_check/.
Two errors came from omitted, unchanged repository fixture files outside fast/.
The three required files were restored byte-for-byte from the pinned git commit.
The portable runner now checks these prerequisites first and sets fast/ as cwd
for the existing subprocess-based CLI test. No production fix was necessary.
