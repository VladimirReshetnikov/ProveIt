#!/usr/bin/env python3
"""Reuse beta*J as q-1: an exact122-operation evaluator, no parent edits."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT/'candidates/ten-positive-scaled-norm-shared'
OUT = ROOT/'candidates/ten-positive-scaled-norm-reuse'
PARENT_SHA = '327296a42616d5646502e9487075be32fe14402dbbad5b2925c8d8ff2718a371'


def need(ok,message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def build():
    files = {}
    raw = (PARENT/'equation.json').read_bytes()
    need(digest(raw) == PARENT_SHA,'complete frozen123-operation parent')
    parent = json.loads(raw)
    files['source/parent-equation.json'] = raw
    files['source/parent-proof.md'] = (PARENT/'README.md').read_bytes()
    files['source/parent-check.json'] = (PARENT/'CHECK.json').read_bytes()
    files['source/parent-check-optimized.json'] = (PARENT/'CHECK_OPTIMIZED.json').read_bytes()
    files['source/parent-provenance.json'] = (PARENT/'PROVENANCE.json').read_bytes()
    files['source/original-proof.md'] = (PARENT/'source/parent/PROOF.md').read_bytes()
    files['source/original-peer.md'] = (PARENT/'source/peer/ten-positive-scaled-norm-peer.md').read_bytes()
    files['source/original-replays.json'] = (PARENT/'source/peer/ten-positive-scaled-norm-peer.json').read_bytes()
    oracle = PARENT/'source/peer/ten-positive-scaled-norm-peer.py'
    files['source/independent_norm_oracle.py'] = oracle.read_bytes()
    old = parent['source']
    deleted = next(i for i,row in enumerate(old) if row[0] == 'qm1')
    need(old[deleted] == ['qm1','-','q',1],'exact removed subtraction')
    need([r for r in old[:deleted] if r[0] == 'q'] == [['q','+','bJ',1]],'earlier exact q=bJ+1')
    child = deepcopy(parent)
    child['name'] = 'p10_positive_degree816_reuse'
    child['parent_sha256'] = digest(raw)
    new = []
    remap = []
    for i,(name,op,a,b) in enumerate(old):
        if i == deleted:
            continue
        a = 'bJ' if a == 'qm1' else a
        b = 'bJ' if b == 'qm1' else b
        remap.append(dict(parent_index=i,child_index=len(new),register=name))
        new.append([name,op,a,b])
    child['source'] = new
    child['operations'] = len(new)
    child['operation_breakdown'] = dict(Counter(r[1] for r in new))
    child['proof_status'] = 'Exact universal polynomial identity with frozen123-operation parent via q-1=(beta*J+1)-1=beta*J; no new Lean/internal-ZFC proof.'
    need(len(new) == 122 and child['operation_breakdown'] == {'*':73,'+':30,'-':19},'actual122-operation census')
    files['equation.json'] = encoded(child)
    files['PREFIX_REMAP.json'] = encoded(dict(schema='complete_gate_alias_remap_v1',parent_sha256=digest(raw),
        alias=dict(deleted_register='qm1',retained_register='bJ',deleted_index=deleted,old_definition=old[deleted],premise=['q','+','bJ',1],identity='(bJ+1)-1=bJ'),
        retained_gates=remap,all_other_operands_unchanged=True,domain='every commutative ring'))
    for name,pin in parent['coefficient_binding']['ports'].items():
        blob = (PARENT/'coefficients'/pin['file']).read_bytes()
        need(digest(blob) == pin['gzip_sha256'],'whole actual coefficient '+name)
        files['coefficients/'+pin['file']] = blob
    files['coefficients/BINDING.json'] = encoded(parent['coefficient_binding'])
    files['PROVENANCE.json'] = encoded(dict(parent_path=str(PARENT.relative_to(ROOT)),parent_equation_sha256=PARENT_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),oracle_sha256=digest(oracle.read_bytes()),
        semantic_change='None: the same generic polynomial over free ports and every specialization, including the separately calibrated BFS44page tuple.',
        page_policy='The published123-operation evaluator remains valid; no page is rerendered for this minor saving.'))
    files['BUILD.json'] = encoded(dict(status='PASS',positive_variables=10,operations=122,exact_degree=816,
        sha256={name:digest(value) for name,value in files.items()}))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    for name,raw in build().items():
        path = OUT/name
        if args.check:
            need(path.read_bytes() == raw,'byte-identical '+name)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,operations=122,exact_degree=816),indent=2))


if __name__ == '__main__':
    main()
