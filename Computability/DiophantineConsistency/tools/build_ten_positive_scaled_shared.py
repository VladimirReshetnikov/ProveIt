#!/usr/bin/env python3
"""One exact associativity saving in the frozen ten-positive degree816 circuit."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
PARENT = ROOT/'candidates/ten-positive-scaled-norm'
DEST = ROOT/'candidates/ten-positive-scaled-norm-shared'
COMMIT = '8380e70262337360af048a88ebcd9c17b4c7808d'
PEER_COMMIT = '022a559984940bb6f3c1e5cca1e48137f649127b'
PEERS = ['ten-positive-scaled-norm-peer.md','ten-positive-scaled-norm-peer.py',
         'ten-positive-scaled-norm-peer.json','ten-positive-scaled-norm-peer-algebra.json',
         'ten-positive-scaled-norm-peer-algebra-optimized.json']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def build():
    files = {}
    originals = {}
    for path in sorted(PARENT.iterdir()):
        if not path.is_file():
            continue
        member = str(path.relative_to(REPO))
        raw = subprocess.run(['git','show',COMMIT+':'+member],cwd=REPO,capture_output=True,check=True).stdout
        need(path.read_bytes() == raw,'original frozen parent '+path.name)
        files['source/parent/'+path.name] = raw
        originals[path.name] = digest(raw)
    for name in PEERS:
        member = str((ROOT/'reviews'/name).relative_to(REPO))
        files['source/peer/'+name] = subprocess.run(['git','show',PEER_COMMIT+':'+member],cwd=REPO,capture_output=True,check=True).stdout
    parent_raw = files['source/parent/p10_positive_degree816.json']
    parent = json.loads(parent_raw)
    old = parent['source']
    deleted = next(i for i,r in enumerate(old) if r[0] == 'Am1I')
    replaced = next(i for i,r in enumerate(old) if r[0] == '4Am1I')
    need(old[deleted] == ['Am1I','*','Am1','I'],'old product exact')
    need(old[replaced] == ['4Am1I','*',4,'Am1I'],'old scaling exact')
    need([r for r in old[:deleted] if r[0] == '4Am1'] == [['4Am1','*',4,'Am1']],'shared earlier scalar product')
    need([r[0] for r in old if 'Am1I' in r[2:]] == ['4Am1I'],'removed product has exactly the claimed use')
    child = deepcopy(parent)
    child['name'] = 'p10_positive_degree816_shared'
    child['source'] = [(['4Am1I','*','4Am1','I'] if i == replaced else r) for i,r in enumerate(old) if i != deleted]
    child['operations'] = len(child['source'])
    child['operation_breakdown'] = dict(Counter(r[1] for r in child['source']))
    child['coefficient_binding']['path'] = 'coefficients/'
    child['parent_sha256'] = digest(parent_raw)
    child['proof_status'] = 'Exact polynomial identity with frozen124-operation parent; unbounded ordinary equivalence inherited; no new Lean/object-ZFC proof.'
    need(child['operations'] == 123 and child['operation_breakdown'] == {'*':73,'+':30,'-':20},'whole new circuit census')
    files['equation.json'] = encoded(child)
    retained = []
    for index,r in enumerate(old):
        if index == deleted:
            continue
        new_index = index-int(index > deleted)
        retained.append(dict(parent_index=index,child_index=new_index,register=r[0]))
    files['PREFIX_REMAP.json'] = encoded(dict(schema='complete_named_gate_remap_v1',parent_sha256=digest(parent_raw),
        deleted_gate=dict(parent_index=deleted,row=old[deleted],restoration=['*','Am1','I']),
        replaced_gate=dict(parent_index=replaced,child_index=replaced-int(replaced>deleted),old_row=old[replaced],new_row=['4Am1I','*','4Am1','I']),
        retained_gates=retained,identity='4*(Am1*I) = (4*Am1)*I',domain='every commutative ring'))
    coefficients = ROOT/'candidates/split116-compact/compact57/coefficients/compact_tuple'
    for name,pin in parent['coefficient_binding']['ports'].items():
        raw = (coefficients/pin['file']).read_bytes()
        need(digest(raw) == pin['gzip_sha256'],'whole authentic fixed port '+name)
        files['coefficients/'+pin['file']] = raw
    files['coefficients/BINDING.json'] = encoded(child['coefficient_binding'])
    provenance = dict(commit=COMMIT,parent_path=str(PARENT.relative_to(REPO)),parent_files=originals,
        parent_equation_sha256=digest(parent_raw),generator_sha256=digest(Path(__file__).read_bytes()),
        peer_commit=PEER_COMMIT,peer_files={name:digest(files['source/peer/'+name]) for name in PEERS},
        scope='Only one associativity cut; complete original source, full normal/-O peer receipts and wholecompact44 payloads retained. No coefficient regeneration or Lean.')
    files['PROVENANCE.json'] = encoded(provenance)
    files['BUILD.json'] = encoded(dict(status='PASS',variables=10,domain='strictly positive integers',
        operations=123,exact_degree=816,sha256={name:digest(raw) for name,raw in files.items()}))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    files = build()
    for name,raw in files.items():
        target = DEST/name
        if args.check:
            need(target.read_bytes() == raw,'byte-identical '+name)
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,operations=123,exact_degree=816),indent=2))


if __name__ == '__main__':
    main()
