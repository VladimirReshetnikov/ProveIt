#!/usr/bin/env python3
"""Check that the provisional AQ26 client is the pinned AQ29 client adapted by name."""
from hashlib import sha256
from pathlib import Path

here = Path(__file__).resolve().parent
reference = here.parent / 'ipra-standard-aq29' / 'draft'
expected = {
    '.lean': '3d5dfcf53162bc7f1334e56d2a1e1735da4eafd2f31307fc0634f2116f77e7e3',
    'Checks.lean': 'd2dc7c8308b9fa2ffed0a981e7486f68362615e718cd791f006ac83007bc30ec',
}
for suffix, digest in expected.items():
    data = (reference / ('IPRAStandardAQ29' + suffix)).read_bytes()
    assert sha256(data).hexdigest() == digest, suffix
    assert (here / 'draft' / ('IPRAStandardAQ26' + suffix)).read_bytes() == data.replace(b'AQ29', b'AQ26'), suffix
print('PASS: provisional AQ26 client exactly adapts the pinned AQ29 client')
