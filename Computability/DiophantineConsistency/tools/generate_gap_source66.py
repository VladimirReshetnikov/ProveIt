#!/usr/bin/env python3
"""Generate literal source66 rows and affine identities from pinned inert JSON.

The existing expression printer is reused; no upstream research code is run.
Lean independently checks every emitted scalar row identity.
"""
from pathlib import Path
import hashlib
import json
import runpy

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'candidates/gap2082-compact54/data/H2082/source.json'
PARENT = ROOT/'data/split59/parent_source.json'
OUTPUT = ROOT/'Lean/DiophantineConsistency/GapSource66.lean'
START = '-- BEGIN GENERATED GAP SOURCE\n'
END = '-- END GENERATED GAP SOURCE\n'


def generate():
    if hashlib.sha256(SOURCE.read_bytes()).hexdigest()!='e4f50dbede42c421defa2d7d36268413351dd1e023763c584ea34f3b9a827957':
        raise ValueError('source66 pin')
    if hashlib.sha256(PARENT.read_bytes()).hexdigest()!='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287':
        raise ValueError('parent59 pin')
    helper = runpy.run_path(str(ROOT/'tools/generate_split_certificate59.py'),run_name='gap_expression_printer')
    source = json.loads(SOURCE.read_text()); parent = json.loads(PARENT.read_text())
    def rows(d):
        return [{tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in d['equations']]
    old = rows(parent)
    old[13] = helper['add'](old[13],old[1])
    old[14] = helper['add'](old[14],old[2])
    expr = helper['expression']
    new = [expr(r) for r in rows(source)]
    previous = [expr(r) for r in old]
    if len(new)!=22 or sum(len(helper['grouping'](r)) for r in rows(source))!=85:
        raise ValueError('22 rows /85 weighted records')
    out = [
        '/-- Literal source66 rows, independently transcribed from its85-record source. -/',
        'def rows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=',
        '  !['+',\n    '.join(new)+']', '']
    for k in range(22):
        # Replace complete scalar atoms; avoid touching x 1 inside x 18.
        import re
        old_value = re.sub(r'\bx (\d+)\b',lambda m:
            '(x 18+x 12+x 13)' if m[1]=='18' else
            '(x 16+(ports 0*x 0+1))' if m[1]=='16' else m[0],previous[k])
        out.extend([
            f'private theorem row_identity_{k} (ports : Fin 4 → R) (x : Fin 31 → R) :',
            f'    rows ports x {k}=SplitCertificate59.transformedRows ports (toOld ports x) {k} := by',
            f'  change {new[k]} = {old_value}',
            '  ring', ''])
    out.extend([
        'theorem row_identity (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :',
        '    rows ports x k=SplitCertificate59.transformedRows ports (toOld ports x) k := by',
        '  fin_cases k'])
    out.extend(f'  · exact row_identity_{k} ports x' for k in range(22))
    return '\n'.join(out)+'\n'


def main():
    text = OUTPUT.read_text()
    before,rest = text.split(START,1)
    _,after = rest.split(END,1)
    OUTPUT.write_text(before+START+generate()+END+after)


if __name__=='__main__':
    main()
