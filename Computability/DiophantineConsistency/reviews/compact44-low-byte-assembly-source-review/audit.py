#!/usr/bin/env python3
"""Read-only finite audit of the unchecked compact low-byte assembly draft."""
import ast
from collections import Counter
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
BASE = DC / 'research/ordinary12-ipra-bridge'
ASSEMBLY = BASE / 'compact44-low-byte-assembly-draft'
CHUNKS = BASE / 'compact44-low-byte-boundary-chunks'
RECIPE = BASE / 'compact44-low-byte-complete-recipe'
PAYLOAD = DC / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads/MC.bin.gz'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def pairs(text):
    return [(int(a), int(b)) for a, b in re.findall(r'\((\d+) ≤ j ∧ j < (\d+)\)', text)]


files = [ASSEMBLY / 'CompactLowByteAssembly.lean', ASSEMBLY / 'generate.py',
         CHUNKS / 'generate.py', RECIPE / 'CompactLowByteRecipeData.lean', RECIPE / 'generate.py',
         BASE / 'compact44-concrete-mask-prototype/CompactConcreteMask.lean',
         BASE / 'compact44-list-mask-prototype/CompactListMask.lean',
         BASE / 'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean',
         BASE / 'compact44-low-byte-dense-prototype/CompactLowByteDense.lean',
         BASE / 'compact44-low-byte-dense-extra-prototype/CompactLowByteDenseExtra.lean',
         BASE / 'compact44-low-byte-gaps-prototype/CompactLowByteGaps.lean',
         BASE / 'compact44-low-byte-prefix-prototype/CompactLowBytePrefix.lean',
         BASE / 'compact44-low-byte-tail-plan/CompactLowByteTail.lean',
         BASE / 'compact44-low-byte-bound-prototype/CompactLowByteBound.lean',
         BASE / 'generic-radix-window-reconstruction-prototype/RadixWindowReconstruction.lean',
         PAYLOAD] + [CHUNKS / f'CompactLowByteBoundary{i:02d}.lean' for i in range(1, 13)]
before = {str(p.relative_to(ROOT)): p.read_bytes() for p in files}
text = lambda path: before[str(path.relative_to(ROOT))].decode('utf-8')
asm = text(ASSEMBLY / 'CompactLowByteAssembly.lean')
recipe = text(RECIPE / 'CompactLowByteRecipeData.lean')
extra = text(BASE / 'compact44-low-byte-dense-extra-prototype/CompactLowByteDenseExtra.lean')
gaps = text(BASE / 'compact44-low-byte-gaps-prototype/CompactLowByteGaps.lean')
dense = text(BASE / 'compact44-low-byte-dense-prototype/CompactLowByteDense.lean')
support_src = re.sub(r'\s+', '', text(BASE / 'compact44-concrete-mask-prototype/CompactConcreteMask.lean'))
mask_src = re.sub(r'\s+', '', text(BASE / 'compact44-list-mask-prototype/CompactListMask.lean'))
ports_src = re.sub(r'\s+', '', text(BASE / 'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean'))

need('((range943∪Ico983993∪Ico10031012∪Ico10131032∪{1063,1064,1095,2195,3296})\\{1})'
     in support_src, 'unexpected support syntax')
need('ifj=specialthenB-4elseifj∈SthenB-2elseB-1' in mask_src, 'unexpected digit definition')
need('deflowNat:ℕ:=Nat.ofDigits(2^67)(CompactListMask.digits(2^67)88071063CompactConcreteMask.support)'
     in ports_src, 'unexpected symbolic low definition')

need('theorem point (j : ℕ) (hj : j < 73759)' in asm and
     'by_cases hp : j < 16' in asm and 'by_cases hd : 17 ≤ j ∧ j < 7890' in asm and
     'by_cases ht : 27613 ≤ j ∧ j < 73751' in asm, 'unexpected assembly branches')
need('have hpow : (256:ℕ)^j = 2^(8*j)' in asm and
     len(re.findall(r'rw \[byteAt,[^\n]*hpow\]', asm)) == 4, 'power rewrite missing')
extra_intervals = pairs(extra[extra.index('def inDenseExtra'):extra.index('theorem extra_dense_byte')])
gap_intervals = pairs(gaps[gaps.index('def inGap'):gaps.index('theorem gap_byte')])
boundary_intervals = pairs(asm[asm.index('have hleft'):asm.index('rcases hleft')])
need(len(extra_intervals) == 3 and len(gap_intervals) == 6 and len(boundary_intervals) == 12,
     'unexpected interval count')
blocks = [('prefix', 0, 16), ('dense', 17, 7890), ('tail', 27613, 73751)]
blocks += [('dense-extra', *x) for x in extra_intervals]
blocks += [('gap', *x) for x in gap_intervals]
blocks += [('boundary', *x) for x in boundary_intervals]
coverage = Counter(j for _, lo, hi in blocks for j in range(lo, hi))
need(set(coverage) == set(range(73759)) and all(n == 1 for n in coverage.values()),
     'assembly intervals have gap, overlap or out-of-range index')
need(sum(hi-lo for lo, hi in boundary_intervals) == 142, 'boundary count mismatch')

with tempfile.TemporaryDirectory(prefix='low-byte-chunk-review-') as temp:
    temp = Path(temp)
    gen = temp / 'generate.py'
    gen.write_bytes(before[str((CHUNKS / 'generate.py').relative_to(ROOT))])
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(gen)], cwd=ROOT,
                         capture_output=True, text=True, timeout=60)
    need(run.returncode == 0 and not run.stderr, ('chunk generator failed', run.stderr))
    report = json.loads(run.stdout)
    need(report['count'] == 142 and len(report['intervals']) == 12, 'bad generator report')
    for i, interval in enumerate(boundary_intervals, 1):
        module = f'CompactLowByteBoundary{i:02d}'
        source = text(CHUNKS / f'{module}.lean')
        need((temp / f'{module}.lean').read_bytes() == source.encode('utf-8'),
             ('generated source mismatch', module))
        need((report['intervals'][i-1]['lower'], report['intervals'][i-1]['upper_exclusive']) == interval and
             f'{module}.windows j h.1 h.2' in asm and
             f'(hlo : {interval[0]} ≤ j) (hhi : j < {interval[1]})' in source and
             '(CompactSymbolicPorts.lowNat / 256^j) % 256' in source,
             ('chunk/assembly contract mismatch', module))

with tempfile.TemporaryDirectory(prefix='low-byte-assembly-review-') as temp:
    temp = Path(temp)
    gen = temp / 'generate.py'
    gen.write_bytes(before[str((ASSEMBLY / 'generate.py').relative_to(ROOT))])
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(gen)], cwd=ROOT,
                         capture_output=True, text=True, timeout=60)
    need(run.returncode == 0 and not run.stderr and
         (temp / 'CompactLowByteAssembly.lean').read_bytes() ==
         before[str((ASSEMBLY / 'CompactLowByteAssembly.lean').relative_to(ROOT))],
         ('assembly generator/source mismatch', run.stderr))

recipe_dense = pairs(recipe[recipe.index('def denseIndex'):recipe.index('instance (j')])
need(recipe_dense == [(17,7890)] + extra_intervals, 'dense intervals disagree')
need(re.search(r'def denseWindow \(r : ℕ\) : ℕ :=\s*(.*?)\n\s*def ', recipe, re.S).group(1).strip() ==
     re.search(r'def denseWindow \(r : ℕ\) : ℕ :=\s*(.*?)\n\s*theorem ', dense, re.S).group(1).strip(),
     'two dense window definitions disagree')
exceptions = {int(i): int(v) for i, v in re.findall(r'if j = (\d+) then (\d+) else',
              recipe[recipe.index('def irregularByte'):recipe.index('def denseIndex')])}
need(len(exceptions) == 11 and 'if j = 0 then 254' in recipe and
     'def bytes : List ℕ := (List.range 73759).map byteAt' in recipe, 'recipe syntax changed')
raw = gzip.decompress(before[str(PAYLOAD.relative_to(ROOT))])
need(len(raw) == 73759 and digest(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
     'retained payload mismatch')

def recipe_value(j):
    if j == 0: return 254
    if any(lo <= j < hi for lo, hi in recipe_dense):
        r = 8*j % 67
        return 254 if r == 0 else 255 - 2**(67-r) if r >= 60 else 255
    return exceptions.get(j, 255)

need(bytes(recipe_value(j) for j in range(len(raw))) == raw, 'recipe does not match raw bytes')
support = (set(range(943)) | set(range(983,993)) | set(range(1003,1012)) |
           set(range(1013,1032)) | {1063,1064,1095,2195,3296}) - {1}
number = ((1 << (67*8807)) - 1 - sum(1 << (67*i) for i in support)
          - 2*(1 << (67*1063)))
need(number.to_bytes(73759, 'little') == raw, 'independent sparse defect value differs')
need(all(p.read_bytes() == before[str(p.relative_to(ROOT))] for p in files), 'source changed during audit')
print(json.dumps({'status': 'SOURCE_AND_FINITE_INTERVAL_CHECK_ONLY',
                  'sources_sha256': {p: digest(data) for p, data in before.items()},
                  'raw_sha256': digest(raw), 'support_cardinality': len(support),
                  'total_indices': len(coverage), 'uncovered': 0, 'overlap': 0,
                  'boundary_intervals': boundary_intervals, 'boundary_indices': 142,
                  'exception_count': len(exceptions), 'recipe_matches_payload': True,
                  'independent_defect_matches_payload': True,
                  'scope': 'external finite/source check; no Lean proof of draft, parser or gzip provenance'},
                 indent=2, sort_keys=True))
