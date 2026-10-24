# Temporary historical ZIP compatibility

The wave11 placement moved delivered files into sources76–110 and removed
the original ZIP paths from `docs/incoming`. Frozen checkers still authenticate
those exact original ZIP bytes. This compatibility wrapper supplies those
paths temporarily without changing any sealed checker, proof or source pin.

`ARCHIVES.json` records all35 directory-backed archive paths, their full
source commit `e13c748234d6e7678fd35c934311a9227e90ef44`, Git blob IDs,
SHA256 hashes, byte lengths, Git modes and placed directories. They total
92,740,099 bytes. The merge removed36 ZIPs: the additional Centered
Compression dependency ZIP was a retired duplicate with no placed directory
and is explicitly excluded from this35-archive wrapper.

Run the wrapper with an ordinary argv command:

```sh
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/encoded-index-sign-profile/check.py --output /tmp/frozen601-normal.json
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B -O Computability/DiophantineConsistency/research/encoded-index-sign-profile/check.py --output /tmp/frozen601-optimized.json
```

The child always runs from the repository root. The wrapper passes argv
directly to `subprocess.Popen`; it does not evaluate a shell command.
Direct lean/lake commands and recursive wrapper invocations are rejected.
The wrapper itself neither extracts archives nor executes their contents.
Lean remains paused.

Before publishing any ZIP, the wrapper authenticates its metadata, exact
commit/tree path, Git blob SHA1, full byte length and SHA256. It refuses
symlink archive parents or archive paths. Existing regular ZIPs with the
expected bytes are preserved; differing files cause failure before any
historical path is created or the child starts. Complete staged files are
published by exclusive hard links, so existing paths are never overwritten
and an interrupted write cannot leave a partial historical ZIP.

An exclusive flock in this worktree's Git directory serializes cooperating
wrappers through child completion and cleanup. SIGINT, SIGTERM and SIGHUP
terminate the child process group and run cleanup. Cleanup removes only
files created by this invocation that still have the same device, inode
and SHA256. Changed or replaced paths are preserved with a stderr notice.
Preexisting files are never removed. Any newly created archive parent
directory is removed only if its identity is unchanged and it is empty.
The child status is forwarded, including conventional signal statuses.

`check.py` copies the exact tool and metadata into an isolated scratch Git
repository with read-only access to the original Git objects. Ten controls
cover successful and failing children, a missing command, literal argv and
repository cwd, preexisting exact/mismatched files, symlink integrity,
changed/replaced created files, interruption cleanup, and concurrent flock
serialization. Normal and optimized modes use explicit checks. They do not
execute code from archives or alter any actual historical archive path.

The recorded actual frozen601 checker runs use the wrapper against the
unchanged accepted74-predicate profile packet. Their receipts are compared
byte for byte with its sealed normal/optimized receipts. These are replay
compatibility results, with no new equation, proof or metric claim.

All records use `.json` or `.txt`. TOOL_PINS.json binds the external wrapper;
MANIFEST.json closes the research packet. No commit is made by this work.
