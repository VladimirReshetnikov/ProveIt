#!/usr/bin/env python3
"""Generate a separate retry replacing each failed range simplifier by decide."""
from pathlib import Path
from hashlib import sha256
H=Path(__file__).resolve().parent
src=H.parent/'direct-bfs-lean-conjugacy-aggregate-prototype/DirectBFSCoverageAggregate.lean'
raw=src.read_bytes()
if sha256(raw).hexdigest()!='0a4d0212368891e0a3b81b030a608dbe14274d40c3a7895e66fa49f55f8ec9fe':raise SystemExit('original source pin changed')
s=raw.decode();old='    simp only [List.range\'_append_1, Nat.reduceAdd]';new='    decide'
if s.count(old)!=7:raise SystemExit('unexpected edit count')
out=H/'DirectBFSCoverageAggregate.lean'
content=s.replace(old,new).encode()
import sys
if sys.argv[1:]==['--check']:
 if out.read_bytes()!=content:raise SystemExit('source differs')
else:
 if out.exists():raise SystemExit('refusing overwrite')
 out.write_bytes(content)
print(sha256(content).hexdigest())
