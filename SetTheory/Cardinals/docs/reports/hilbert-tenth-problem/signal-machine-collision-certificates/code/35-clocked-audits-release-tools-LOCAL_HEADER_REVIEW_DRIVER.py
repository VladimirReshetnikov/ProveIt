#!/usr/bin/env python3
"""Inspect one freshly authored local-only ZIP-extra regression."""
from pathlib import Path
import hashlib
import json
import struct
import subprocess
import sys
import zipfile

D = Path(__file__).resolve().parent / 'delta'
base = D / 'repeat-a.zip'
pin = json.loads((D / 'owned-manifest-pin.json').read_text())['manifest_sha256']
data = bytearray(base.read_bytes())
with zipfile.ZipFile(base) as z:
    target = z.getinfo('Report65/README.md')
    local_offset = target.header_offset
old_end = data.rfind(b'PK\x05\x06')
central_start = struct.unpack_from('<I', data, old_end + 16)[0]
name_len, old_extra_len = struct.unpack_from('<HH', data, local_offset + 26)
assert old_extra_len == 0
insert = local_offset + 30 + name_len
extra = b'\xfe\xca\x00\x00'
struct.pack_into('<H', data, local_offset + 28, len(extra))
data[insert:insert] = extra
at = central_start + len(extra)
while data[at:at+4] == b'PK\x01\x02':
    name_len, extra_len, comment_len = struct.unpack_from('<HHH', data, at + 28)
    assert extra_len == 0
    old_offset = struct.unpack_from('<I', data, at + 42)[0]
    if old_offset > local_offset:
        struct.pack_into('<I', data, at + 42, old_offset + len(extra))
    at += 46 + name_len + extra_len + comment_len
assert data[at:at+4] == b'PK\x05\x06'
struct.pack_into('<I', data, at + 16, central_start + len(extra))
path = D / 'mutant-archives/genuine-local-only-extra.zip'
with path.open('xb') as f:
    f.write(data)
with zipfile.ZipFile(path) as z:
    assert all(not i.extra for i in z.infolist())
    assert z.read('Report65/README.md') == (D / 'owned-release/README.md').read_bytes()
cmd = [sys.executable, '-I', str(D / 'owned-release/tools/release65.py'), 'archive-check', '--archive', str(path), '--manifest-sha256', pin]
r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
(D / 'logs/genuine-local-only-extra.txt').write_bytes(r.stdout)
result = {'name': 'genuine-local-only-extra', 'argv': cmd, 'exit_code': r.returncode,
          'pass': r.returncode != 0 and b'Noncanonical local ZIP extra field' in r.stdout,
          'central_extra_fields_empty': True, 'unmodified_member_content_readable': True,
          'archive_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
with (D / 'LOCAL_HEADER_RESULT.json').open('x') as f:
    json.dump(result, f, indent=2)
print(json.dumps(result, indent=2))
