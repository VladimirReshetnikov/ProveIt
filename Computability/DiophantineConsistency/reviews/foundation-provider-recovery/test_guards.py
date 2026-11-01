#!/usr/bin/env python3
"""Exercise provider import guards with a small isolated fake search path."""
from pathlib import Path
import tempfile
from unittest.mock import patch
import build_all as build

def rejected(action):
    try:
        action()
    except RuntimeError:
        return
    raise AssertionError('guard accepted a changed dependency')

with tempfile.TemporaryDirectory(prefix='foundation-guard-test-') as tmp:
    root = Path(tmp)
    source = root / 'lib/FormalizedFormalLogic-Foundation/Foundation'
    source.mkdir(parents=True)
    (source / 'A.lean').write_text('import Mathlib.Foo\n')
    early, own, late = root / 'early', root / '.lake/build/lib/lean', root / 'late'
    (late / 'Mathlib').mkdir(parents=True)
    obj = late / 'Mathlib/Foo.olean'
    obj.write_bytes(b'original')
    with patch.object(build.subprocess, 'check_output', return_value=f'{early}:{own}:{late}'):
        sources, external, guard, _ = build.direct_external_inputs(root, ['Foundation.A'], {})
    assert sources == ['Foundation.A'] and external == ['Mathlib.Foo']
    build.check_guard(guard)

    (early / 'Mathlib').mkdir(parents=True)
    shadow = early / 'Mathlib/Foo.olean'
    shadow.write_bytes(b'shadow')
    rejected(lambda: build.check_guard(guard))
    shadow.unlink()
    obj.write_bytes(b'changed')
    rejected(lambda: build.check_guard(guard))
    obj.write_bytes(b'original')
    companion = Path(str(obj) + '.server')
    companion.write_bytes(b'new')
    rejected(lambda: build.check_guard(guard))
    companion.unlink()
    (late / 'Foundation').mkdir()
    foreign = late / 'Foundation/A.olean'
    foreign.write_bytes(b'foreign')
    rejected(lambda: build.check_guard(guard))
    foreign.unlink()
    foreign_companion = late / 'Foundation/A.olean.private'
    foreign_companion.write_bytes(b'foreign companion')
    rejected(lambda: build.check_guard(guard))
    foreign_companion.unlink()
    for bad_path in (f'{early}::{late}', f'{early}:relative:{late}'):
        with patch.object(build.subprocess, 'check_output', return_value=bad_path):
            rejected(lambda: build.direct_external_inputs(root, ['Foundation.A'], {}))

print('PASS: shadow, changed object, new companion, foreign Foundation and bad paths rejected')
