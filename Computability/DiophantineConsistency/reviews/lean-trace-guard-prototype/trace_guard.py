#!/usr/bin/env python3
"""Fail-closed post-run classification of selected strace file-open events.

Requires: strace -f -qq -yy -xx -s 4096 -e trace=open,openat,openat2,execve,execveat
This is a planning/observability tool, not proof of an immutable runtime.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat

CALL = re.compile(r'^(\d+)\s+(open|openat|openat2|execve|execveat)\((.*)\)\s+=\s+(-?\d+)(?:<(.*)>)?(?:\s.*)?$')
UNFINISHED = re.compile(r'^(\d+)\s+(open|openat|openat2|execve|execveat)\((.*) <unfinished \.\.\.>$')
RESUMED = re.compile(r'^(\d+)\s+<\.\.\. (open|openat|openat2|execve|execveat) resumed>(.*)$')
QUOTED = re.compile(r'"((?:\\.|[^"\\])*)"')
HEX = re.compile(r'(?:\\x[0-9a-fA-F]{2})*\Z')

class TraceError(ValueError):
    pass

def decode(token):
    if not HEX.fullmatch(token):
        raise TraceError('path is truncated, not -xx encoded, or otherwise unsupported')
    value = os.fsdecode(bytes.fromhex(token.replace('\\x', '')))
    if '\x00' in value:
        raise TraceError('NUL in path')
    return value

def normalize(raw):
    pending = {}
    for line in raw.splitlines():
        if not line.strip():
            continue
        m = UNFINISHED.fullmatch(line)
        if m:
            key = (m[1], m[2])
            if key in pending:
                raise TraceError(('duplicate unfinished call', key))
            pending[key] = f'{m[1]} {m[2]}({m[3]}'
            continue
        m = RESUMED.fullmatch(line)
        if m:
            key = (m[1], m[2])
            if key not in pending:
                raise TraceError(('resumed call without start', key))
            yield pending.pop(key) + m[3]
            continue
        if line.startswith('strace:') or '+++ exited with' in line or '--- SIG' in line:
            raise TraceError(('unexpected tracer/exit/signal line', line))
        yield line
    if pending:
        raise TraceError(('unfinished calls', sorted(pending)))

def roots_from_policy(policy):
    roots = []
    for row in policy['roots']:
        if not row.get('role') or not Path(row['path']).is_absolute():
            raise TraceError(('bad policy root', row))
        path = Path(row['path']).resolve(strict=True)
        if not path.is_dir():
            raise TraceError(('policy root is not directory', row))
        if path == Path('/') and not policy.get('allow_broad_root_for_smoke', False):
            raise TraceError('filesystem root policy requires explicit smoke-test override')
        roots.append((path, row['role']))
    if len({p for p, _ in roots}) != len(roots):
        raise TraceError('duplicate resolved policy root')
    return sorted(roots, key=lambda pair: len(pair[0].parts), reverse=True)

def analyze(raw, policy):
    roots = roots_from_policy(policy)
    special_allowed = {Path(p).resolve(strict=True) for p in policy.get('special_paths', [])}
    events = []
    hash_cache = {}
    for line in normalize(raw):
        m = CALL.fullmatch(line)
        if not m:
            raise TraceError(('unrecognized or truncated trace line', line[:180]))
        pid, name, args, result, returned_fd = m.groups()
        if int(result) < 0:
            continue
        strings = list(QUOTED.finditer(args))
        if not strings:
            raise TraceError(('successful call has no path string', name))
        text = decode(strings[0].group(1))
        if not text:
            raise TraceError(('empty path or AT_EMPTY_PATH', name))
        if os.path.isabs(text):
            lexical = Path(text)
        else:
            if name not in ('openat', 'openat2', 'execveat'):
                raise TraceError(('relative path without proven directory', name, text))
            prefix = args[:strings[0].start()].strip()
            match = re.fullmatch(r'(?:AT_FDCWD|\d+)<([^>]*)>,', prefix)
            if not match:
                raise TraceError(('relative path with unresolved dirfd', name, text))
            directory = decode(match[1])
            if not os.path.isabs(directory):
                raise TraceError(('nonabsolute dirfd annotation', directory))
            lexical = Path(directory) / text
        resolved = lexical.resolve(strict=True)
        if returned_fd is not None and name in ('open', 'openat', 'openat2'):
            annotated = decode(returned_fd.split('<', 1)[0])
            if not os.path.isabs(annotated) or Path(annotated) != resolved:
                raise TraceError(('opened fd path disagrees with current resolution', text, annotated, str(resolved)))
        elif name in ('open', 'openat', 'openat2'):
            raise TraceError(('successful open missing -yy fd annotation', text))
        role = next((role for root, role in roots if resolved.is_relative_to(root)), None)
        if role is None:
            raise TraceError(('opened path outside allowed resolved roots', str(resolved)))
        info = resolved.stat()
        if stat.S_ISREG(info.st_mode):
            key = (str(resolved), info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
            if key not in hash_cache:
                hash_cache[key] = hashlib.sha256(resolved.read_bytes()).hexdigest()
            digest = hash_cache[key]
            after = resolved.stat()
            if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns) != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
                raise TraceError(('path mutated during hashing', str(resolved)))
            kind = 'regular'
        elif stat.S_ISDIR(info.st_mode):
            kind, digest = 'directory', None
        elif resolved in special_allowed:
            kind, digest = 'explicitly_allowed_special', None
        else:
            raise TraceError(('special or unsupported opened file', str(resolved)))
        events.append({'pid': int(pid), 'call': name, 'requested': str(lexical),
                       'resolved': str(resolved), 'role': role, 'kind': kind,
                       'sha256_after_run': digest,
                       'may_write': bool(re.search(r'\b(O_WRONLY|O_RDWR|O_TRUNC|O_CREAT|O_TMPFILE)\b', args))})
    if not events:
        raise TraceError('no successful observed events')
    return events

def main():
    p = argparse.ArgumentParser()
    p.add_argument('trace', type=Path)
    p.add_argument('policy', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    raw = args.trace.read_text()
    policy = json.loads(args.policy.read_text())
    events = analyze(raw, policy)
    report = {'status': 'CLASSIFIED_POST_RUN', 'trace_sha256': hashlib.sha256(raw.encode()).hexdigest(),
              'policy_sha256': hashlib.sha256(args.policy.read_bytes()).hexdigest(), 'events': events,
              'scope': 'Successful selected file-open/exec syscalls observed by strace only; '
                       'post-run hashes do not prove compile-time immutability or complete dynamic provenance.'}
    with args.output.open('x') as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write('\n')
    print('CLASSIFIED_POST_RUN', len(events), flush=True)

if __name__ == '__main__':
    main()
