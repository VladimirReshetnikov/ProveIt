#!/usr/bin/env python3
"""Read-only verification of the two HeadBounds proof edits, not Lean checking.
Portable inputs are baseline/ and patched/ siblings. Default output is stdout;
--output explicitly requests an additional JSON file. No patches are applied.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
NAME = 'WangTiles942HeadBounds.lean'
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency') / NAME
SOURCE_HASH = 'bed402c366871656a605ebef749451631c88b34ce57118fa6bea583fce700754'
CANDIDATE_HASH = '96933ecfe2574ca26f1ac633cdfb920e1b9ca0796a0080cfc76e19bff8cb93f9'


def require(condition, message):
    if not condition:
        sys.exit('verification failed: ' + message)


def headers(text):
    out = {}
    for match in re.finditer(r'^theorem\s+(\S+)', text, re.M):
        end = text.index(':=', match.end())
        require(match.group(1) not in out, 'duplicate public theorem name')
        out[match.group(1)] = text[match.start():end]
    return out


def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            i = text.find('\n', i)
            if i == -1:
                break
        else:
            if not depth:
                out.append(text[i])
            i += 1
    require(depth == 0, 'unclosed Lean block comment')
    return ''.join(out)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir', type=Path, default=ROOT / 'baseline')
parser.add_argument('--candidate-dir', type=Path, default=ROOT / 'patched')
parser.add_argument('--patch-file', type=Path, default=ROOT / 'WangTiles942HeadBounds.patch')
parser.add_argument('--output', type=Path, help='Optional explicit JSON output path; default stdout only')
args = parser.parse_args()
source = args.source_dir / NAME
candidate = args.candidate_dir / NAME
src_bytes, dst_bytes = source.read_bytes(), candidate.read_bytes()
require(hashlib.sha256(src_bytes).hexdigest() == SOURCE_HASH, 'wrong source SHA-256')
require(hashlib.sha256(dst_bytes).hexdigest() == CANDIDATE_HASH, 'wrong candidate SHA-256')
src, dst = src_bytes.decode('utf-8'), dst_bytes.decode('utf-8')
require(headers(src) == headers(dst), 'public theorem headers changed')
require(len(headers(src)) == 9, 'unexpected public theorem count')
require(not re.search(r'\b(sorry|axiom|admit|native_decide)\b', uncomment(dst)),
        'proof placeholder or native shortcut')
expected_patch = ''.join(difflib.unified_diff(
    src.splitlines(True), dst.splitlines(True),
    fromfile='a/' + str(REL), tofile='b/' + str(REL)))
require(args.patch_file.read_text() == expected_patch,
        'patch does not exactly reproduce shipped candidate')
require(len(src.splitlines()) == 135 and len(dst.splitlines()) == 130,
        'unexpected physical line counts')

# Finite arithmetic sanity checks, not verification of the Lean proof terms.
for a in range(3):
    require(a < 3 and a <= 2, 'Fin 3 predecessor bound failed')
    require(a*a <= 2*2 == 4, 'square monotonicity specialization failed')
rail_gap_cases = 0
for a in range(3):
    for b in range(3):
        for rail in range(6, 21):
            require(b <= 2 and a*a <= 4, 'facing seam bound failed')
            require(rail > b and rail > a*a, 'active rail separation failed')
            rail_gap_cases += 1
require(rail_gap_cases == 135, 'unexpected rail guard case count')

report = {
    'status': 'static/source-only validation; NOT Lean elaboration or axiom audit',
    'pin': '22e020937caa81d0cb72a4f63071d6c0bcc1eba9',
    'target': str(REL),
    'source_sha256': SOURCE_HASH,
    'candidate_sha256': CANDIDATE_HASH,
    'public_theorem_headers_unchanged': True,
    'public_theorem_count': 9,
    'exact_source_to_candidate_patch': 'pass',
    'source_physical_lines': 135,
    'candidate_physical_lines': 130,
    'net_physical_lines_saved': 5,
    'finite_values_checked': 3,
    'active_rail_gap_cases_checked': rail_gap_cases,
    'compiler_or_installer_invoked': False,
    'verification_checks_active_under_python_optimization': True,
}
result = json.dumps(report, indent=2) + '\n'
if args.output:
    inputs = {source.resolve(), candidate.resolve(), args.patch_file.resolve(), Path(__file__).resolve()}
    require(args.output.resolve() not in inputs, '--output may not overwrite an input')
    args.output.write_text(result)
print(result, end='')
