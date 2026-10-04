#!/usr/bin/env python3
"""Parse retained TeX recorder text independently; no scientific code execution."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).absolute().parent
def need(ok, message):
    if not ok:
        raise ValueError(message)

def verify(folder):
    lock = json.loads((folder / 'BUILD_DEPENDENCIES.json').read_bytes())
    recorded = json.loads((folder / 'RECORDER_INPUT_UNION.json').read_bytes())
    union, local, counts = set(), {}, {}
    for label in ('format', 'compile-1', 'compile-2', 'compile-3'):
        data = (folder / (label + '.fls')).read_bytes()
        lines = data.decode().splitlines()
        pwd = [Path(line[4:]) for line in lines if line.startswith('PWD ')]
        need(len(pwd) == 1, 'Ambiguous recorder PWD')
        work = pwd[0].parent if label == 'format' else pwd[0]
        need(work.parent == folder and work.name.startswith('arity_article-typeset-'), 'Nonisolated TeX work directory')
        external, within = set(), set()
        for line in lines:
            if not line.startswith('INPUT '):
                continue
            p = Path(line[6:])
            p = (p if p.is_absolute() else pwd[0] / p).resolve()
            if p == work or work in p.parents:
                within.add(str(p.relative_to(work)))
            else:
                need(any(str(p).startswith(prefix) for prefix in ('/usr/share/texlive/', '/usr/share/texmf/', '/etc/texmf/', '/var/lib/texmf/')), 'Unexpected external recorder input')
                content = p.read_bytes()
                need(lock['system_inputs'][str(p)] == {'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()}, 'Recorder input pin mismatch')
                external.add(str(p))
        rec = [r for r in recorded['passes'] if r['pass'] == label]
        need(len(rec) == 1 and rec[0]['system_inputs'] == sorted(external), 'Recorder receipt does not describe actual pass')
        need(rec[0]['fls_sha256'] == hashlib.sha256(data).hexdigest(), 'Recorder receipt hash mismatch')
        if label != 'format':
            need('cache/pdflatex.fmt' in within and 'article.tex' in within, 'Fresh local format or article not consumed')
        local[label], counts[label] = sorted(within), len(external)
        union.update(external)
    for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
        p = Path((folder / ('map-' + name + '.stdout')).read_text().strip()).resolve()
        content = p.read_bytes()
        need(lock['system_inputs'][str(p)] == {'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()}, 'Selected font map pin mismatch')
        union.add(str(p))
    need(union == set(lock['system_inputs']) == set(recorded['union']), 'Actual recorder plus selected map union differs from exact lock')
    return {'status': 'PASS', 'actual_recorder_pass_external_counts': counts,
            'actual_input_union_count': len(union), 'isolated_local_inputs': local,
            'fresh_local_format_consumed_in_every_compile': True}

results = {name: verify(ROOT / name) for name in ('locked-build', 'relocated-build')}
(ROOT / 'RECORDER_REVIEW.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
print(json.dumps(results, indent=2, sort_keys=True))
