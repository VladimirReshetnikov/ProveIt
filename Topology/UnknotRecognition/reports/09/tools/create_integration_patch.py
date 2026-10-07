#!/usr/bin/env python3
"""Create an ordinary git-apply patch for the pinned ProveIt fast subtree."""
from __future__ import annotations
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PREFIX='Topology/UnknotRecognition/fast/'


def source_files(base):
    return {p.relative_to(base).as_posix():p for p in base.rglob('*')
            if p.is_file() and '__pycache__' not in p.parts
            and p.suffix not in ('.pyc','.pyo')}


def main():
    before=source_files(ROOT/'baseline/fast')
    after=source_files(ROOT/'fast')
    chunks=[];changed=[]
    for name in sorted(before.keys()|after.keys()):
        old=before[name].read_bytes() if name in before else b''
        new=after[name].read_bytes() if name in after else b''
        if old==new:continue
        a='a/'+PREFIX+name;b='b/'+PREFIX+name
        chunks.append(f'diff --git {a} {b}\n')
        if name not in before:chunks.append('new file mode 100644\n')
        elif name not in after:chunks.append('deleted file mode 100644\n')
        diff=difflib.unified_diff(old.decode().splitlines(keepends=True),
                                 new.decode().splitlines(keepends=True),
                                 fromfile=a if name in before else '/dev/null',
                                 tofile=b if name in after else '/dev/null')
        for line in diff:
            chunks.append(line)
            if not line.endswith('\n'):chunks.append('\n\\ No newline at end of file\n')
        changed.append({'path':PREFIX+name,'operation':'modify' if name in before else 'add',
                        'before_sha256':hashlib.sha256(old).hexdigest() if old else None,
                        'after_sha256':hashlib.sha256(new).hexdigest() if new else None})
    target=ROOT/'integration';target.mkdir(exist_ok=True)
    (target/'fastunknot-0.3.patch').write_text(''.join(chunks))
    (target/'changed_files.json').write_text(json.dumps(changed,indent=2)+'\n')
    print(f'Created patch for {len(changed)} changed or added files.')


if __name__=='__main__':main()
