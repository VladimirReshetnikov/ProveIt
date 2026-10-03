#!/usr/bin/env python3
"""Pin reviewed proof inputs and verify portability-only script adaptation."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parents[1]
rows=(root/'audit/audited-proof-sha256.txt').read_text().splitlines()
for line in rows:
    h,p=line.split('  ',1)
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
original=(root/'audit/verify_p3_p4_direct-original.py').read_text()
portable=(root/'audit/verify_p3_p4_direct.py').read_text()
expected=original.replace("ROOT=Path('/workspace/shared/a202061-allorders-research/action-expansion')", "ROOT=Path(__file__).resolve().parents[1]\nSOURCE_FILES={'proof.md':ROOT/'proofs/action-expansion.md', 'generate_action_polynomials.py':ROOT/'checks/generate_action_polynomials.py'}").replace('(ROOT/filename).read_bytes()', 'SOURCE_FILES[filename].read_bytes()')
assert portable==expected,'Independent P3/P4 mathematics changed during portability adaptation'
print(f'PASS: all {len(rows)} reviewed proof inputs; independent P3/P4 script has source-location-only adaptation')
