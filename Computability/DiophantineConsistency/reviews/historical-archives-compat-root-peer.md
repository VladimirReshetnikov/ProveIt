# Root review: temporary historical archive compatibility

Placement240bf9e422 removed incoming ZIP paths used by already sealed
checkers. Root read the complete202-line wrapper,142-line integrity checker,
metadata and README. The tool authenticates exact full e13 commit/tree/blob,
SHA256 and lengths before publishing complete files by exclusive hard links.
It invokes argv directly, serializes cooperating wrappers with a worktree
Git-directory lock, forwards child status and handles interrupts. Existing
files/symlinks are never overwritten. Cleanup checks ownership by device,
inode and content, preserving changed/replaced paths. No sealed proof,
checker, source pin or equation is edited.

Root replayed all10 isolated integrity controls in both Python modes; both
receipts exactly match their sealed records. The controls cover literal argv
and cwd, child failure, missing commands, preexisting exact/mismatched files,
symlinks, modified/replaced created files, interruption and concurrent lock
lifetimes. The author's actual frozen601 normal/optimized replays match
its old sealed receipts byte for byte. This is a reproducibility repair,
with no new mathematical proof or size claim. All14 closed-packet members
and the external tool binding are hash-correct and unignored.

The35 directory-backed ZIPs total92740099 bytes. The extra retired duplicate
removed by the merge has no placed directory and is explicitly excluded.
New intake readers can instead read exact Git blobs in memory. Old sealed
commands requiring physical paths should be run through this wrapper; their
historical printed commands and bytes remain preserved. Lean remains paused.

ToolSHA256f33095a4501ebb947387087cc476ea28da9801b02be85e289fab17c66e261fea.
Manifest1d4e7f6a8e72b6b053e9c10e4693e825ffa007238358b7298b301fc7aa06b111.
