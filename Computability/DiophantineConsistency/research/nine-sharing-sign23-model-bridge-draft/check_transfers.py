#!/usr/bin/env python3
"""Check the proposed Delta-transfer expression and row-offset transcriptions."""
import contextlib
import hashlib
import io
import json
import runpy
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign24-octic-q3-candidate/seed.json'
new_path = here.parent / 'nine-sharing-sign23-octic-delta-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
assert digest(new_path) == 'ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41'
# Reuse the preceding author's parser, including its own pinned-AST checks.
with contextlib.redirect_stdout(io.StringIO()):
    parser = runpy.run_path(str(here.parent / 'nine-sharing-sign24-model-bridge-draft/check_transfers.py'))['parse']
old, new = json.loads(old_path.read_bytes()), json.loads(new_path.read_bytes())
old_rows, new_rows = old['residuals'], new['residuals']
assert len(old_rows) == 15 and len(new_rows) == 14 and old_rows[3]['gate'] == 'Delta'
indices = [i for i in range(15) if i != 3]
files = [here / f'Sign23Transfers{i:02}.lean' for i in range(2)]
sources = [p.read_text() for p in files]
for new_i, old_i in enumerate(indices):
    a, b, text = old_rows[old_i], new_rows[new_i], sources[new_i // 7]
    name = a['gate']
    assert name == b['gate']
    for side, row, dimension, ix, seed in [('old', a, 25, old_i, 'SharingSeed24Octic'),
                                            ('new', b, 24, new_i, 'SharingSeed23Octic')]:
        prefix = f'def {side}{name} (p : Fin 4 → ℤ) : Expr (Fin {dimension}) :=\n  '
        assert text.count(prefix) == 1
        assert parser(text.split(prefix, 1)[1].split('\n', 1)[0]) == row['expr']
        claim = (f'{seed}.firstResidual p = {side}{name} p' if ix == 0 else
                 f'(({seed}.remainingResiduals p).drop {ix-1}).head? = some ({side}{name} p)')
        assert claim in text
    assert text.count(f'theorem {name}_eval ') == 1
for text in sources: assert 'sorry' not in text and 'admit' not in text
print(json.dumps({'status': 'PASS_SOURCE_ROWS_ONLY', 'transfers': 14,
                  'source_sha256': {p.name: digest(p) for p in files},
                  'scope': 'AST and row-offset transcription, not Lean or an all-model bridge'},
                 sort_keys=True, indent=2))
