#!/usr/bin/env python3
"""Fail-closed synthetic controls for the two independent-audit receipt schemas."""
import importlib.util
import os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
p=Path(__file__).resolve().with_name('replay.py')
s=importlib.util.spec_from_file_location('checked_replay',p)
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for module,key,other in (('CompactListMask','author_receipt_sha256','receipt_sha256'),('CompactConcreteMask','receipt_sha256','author_receipt_sha256')):
    for good in ({key:'expected'}, {key:'expected',other:'expected'}):
        if m.checked_receipt_digest(good,module)!='expected':raise ValueError(('accepted digest mismatch',module))
    for bad in ({},{other:'expected'},{key:'expected',other:'conflict'}):
        try:m.checked_receipt_digest(bad,module)
        except ValueError:pass
        else:raise ValueError(('accepted malformed schema',module,bad))
    if m.checked_receipt_digest({key:'wrong'},module)=='expected':raise ValueError(('accepted wrong digest',module))
print('PASS_EXACT_RECEIPT_KEY_CONTROLS')
