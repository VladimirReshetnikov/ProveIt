#!/usr/bin/env python3
"""Read-only static measurement by default; never elaborates Lean.

The packaged layout has `baseline` beside the `wang` directory. Use
--baseline REPOSITORY_ROOT to override. Optional --output writes JSON;
--write-proposals DIRECTORY explicitly regenerates the proposed module/patch.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', type=Path, default=ROOT.parent / 'baseline')
parser.add_argument('--output', type=Path)
parser.add_argument('--write-proposals', type=Path)
args = parser.parse_args()
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Boundary.lean')

def require(condition, message):
    if not condition:
        raise ValueError(message)

source = (args.baseline / REL).read_text()
require(hashlib.sha256(source.encode()).hexdigest() ==
        'efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c',
        'Boundary baseline differs from the pinned source; review instead of silently remeasuring.')
candidate = (ROOT / 'proposals/BoundaryFibers.lean').read_text()
names = ['north_435_iff_start', 'north_434_iff_initLeft', 'north_436_iff_initializers',
         'north_438_iff_reset', 'north_437_iff_seam', 'south_438_iff_finish',
         'south_437_iff_seam', 'south_reset_iff']

def decl(text, name):
    marker = 'theorem ' + name + ' '
    require(text.count(marker) == 1, 'Expected exactly one declaration: ' + name)
    start = text.index(marker)
    end = text.find('\n\n', start)
    return text[start:end if end != -1 else len(text)]

def body(text):
    require(':= by\n' in text, 'Expected tactic proof body.')
    return text.split(':= by\n', 1)[1]

patched = source
metrics = []
for name in names:
    old = decl(source, name)
    new = decl(candidate, name + '_short')
    require(bool(body(new).strip()), 'Empty candidate proof body: ' + name)
    metrics.append({'theorem': name,
                    'original_body_nonblank_lines': sum(bool(x.strip()) for x in body(old).splitlines()),
                    'candidate_body_nonblank_lines': sum(bool(x.strip()) for x in body(new).splitlines())})
    patched = patched.replace(old, old.split(':= by\n', 1)[0] + ':= by\n' + body(new))
helpers = '\n\n'.join(decl(candidate, n) for n in ['high_north_fiber', 'high_south_fiber']) + '\n\n'
patched = patched.replace('theorem north_435_iff_start ', helpers + 'theorem north_435_iff_start ', 1)
patch = ''.join(difflib.unified_diff(source.splitlines(keepends=True), patched.splitlines(keepends=True),
                                    fromfile='a/' + str(REL), tofile='b/' + str(REL)))
if args.write_proposals is not None:
    args.write_proposals.mkdir(parents=True, exist_ok=True)
    (args.write_proposals / 'WangTiles942Boundary.proposed.lean').write_text(patched)
    (args.write_proposals / 'boundary_fibers.patch').write_text(patch)
summary = {'baseline_commit': 'b310142330df89e48413c8fce62e7de223e1c7d5',
           'source_path': str(REL), 'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
           'metrics_kind': 'static nonblank proof body lines; not runtime or kernel validation',
           'theorems': metrics,
           'original_selected_body_nonblank_lines': sum(x['original_body_nonblank_lines'] for x in metrics),
           'candidate_selected_body_nonblank_lines': sum(x['candidate_body_nonblank_lines'] for x in metrics),
           'new_helpers_body_nonblank_lines': sum(sum(bool(x.strip()) for x in body(decl(candidate,n)).splitlines()) for n in ['high_north_fiber','high_south_fiber']),
           'new_helpers_entire_nonblank_lines': sum(bool(x.strip()) for x in helpers.splitlines()),
           'original_module_nonblank_lines': sum(bool(x.strip()) for x in source.splitlines()),
           'candidate_module_nonblank_lines': sum(bool(x.strip()) for x in patched.splitlines()),
           'original_module_physical_lines': len(source.splitlines()),
           'candidate_module_physical_lines': len(patched.splitlines()),
           'original_module_bytes': len(source.encode()),
           'candidate_module_bytes': len(patched.encode()),
           'candidate_module_sha256': hashlib.sha256(patched.encode()).hexdigest(),
           'lean_compilation': 'NOT RUN',
           'baseline_modified': False}
rendered = json.dumps(summary, indent=2) + '\n'
if args.output is not None:
    args.output.write_text(rendered)
print(rendered, end='')
