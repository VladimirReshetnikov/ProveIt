#!/usr/bin/env python3
"""Delete two exact subtraction aliases from the frozen147/568 integer graph."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARCHIVE = REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
ARCHIVE_SHA = '37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0'
PREFIX = 'ConZFC_Constructive_Reductions_2026-10-23/integer14/'
PARENT_SHA = '10327b2f4fc1589a86268583b1cdc3e59391b32051cecc5f1bf7140c6dea4269'
OUT = ROOT/'candidates/constructive-integer14-shared'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def build():
    archive_raw = ARCHIVE.read_bytes()
    need(digest(archive_raw) == ARCHIVE_SHA,'complete immutable archive')
    with zipfile.ZipFile(ARCHIVE) as z:
        component = {name[len(PREFIX):]:z.read(name) for name in z.namelist()
                     if name.startswith(PREFIX) and not name.endswith('/')}
    need(len(component) == 104,'complete immutable integer component inventory')
    raw = component['crt14_degree568.json']
    need(digest(raw) == PARENT_SHA,'complete147-operation parent')
    parent = json.loads(raw)
    old = parent['nodes']
    need(old[41] == ['sub',25,22] and old[25] == ['add',22,24] and
         old[22] == ['integer',1] and old[24] == ['mul',14,23], 'exact first cancellation')
    need(old[68] == ['sub',67,22] and old[67] == ['add',22,66] and
         old[66] == ['mul',38,65], 'exact second cancellation')
    aliases = {41:24,68:66}
    nodes, mapping = [], {}
    for i,row in enumerate(old):
        if i in aliases:
            mapping[i] = mapping[aliases[i]]
            continue
        mapping[i] = len(nodes)
        nodes.append([row[0],mapping[row[1]],mapping[row[2]]]
                     if row[0] in ('add','sub','mul') else deepcopy(row))
    child = deepcopy(parent)
    child['name'] = 'crt14_degree568_shared'
    child['nodes'] = nodes
    child['output'] = mapping[parent['output']]
    child['named_registers'] = {name:mapping[i] for name,i in parent['named_registers'].items()}
    child['operation_counts'] = dict(Counter(row[0] for row in nodes if row[0] in ('add','sub','mul')))
    child['operations'] = sum(child['operation_counts'].values())
    child['coefficient_binding'] = 'coefficients/BINDING.json'
    child['proof'] = 'README.md'
    child['parent_sha256'] = PARENT_SHA
    child['proof_status'] = 'Exact universal full-polynomial identity by two complete node alias remaps; inherited ordinary integer proof unchanged. No Lean/internal-ZFC proof.'
    need(len(nodes) == 173 and child['operations'] == 145 and
         child['operation_counts'] == {'add':30,'mul':88,'sub':27},'actual complete145-operation graph')
    files = {'equation.json':encoded(child),'source/parent-equation.json':raw}
    for name in ('README.md','PROOF.md','LICENSE','SOURCE_PINS.json'):
        files['source/parent/'+name] = component[name]
    files['source/ordinary-peer.md'] = (ROOT/'reviews/constructive-integer14-peer.md').read_bytes()
    for target,source in (
        ('source/original-review.json','data/constructive-integer14-review.json'),
        ('source/original-review-optimized.json','data/constructive-integer14-review-optimized.json'),
        ('source/independent_norm_oracle.py','reviews/ten-positive-scaled-norm-peer.py'),
    ):
        files[target] = (ROOT/source).read_bytes()
    binding = json.loads(component['upstream/coefficients/BINDING.json'])
    files['coefficients/BINDING.json'] = component['upstream/coefficients/BINDING.json']
    for name,record in binding['payloads'].items():
        files['coefficients/'+record['file']] = component['upstream/coefficients/'+record['file']]
    files['NODE_REMAP.json'] = encoded(dict(schema='complete_integer_dag_alias_remap_v1',
        parent_sha256=PARENT_SHA,
        all_parent_nodes=[dict(parent=i,child=mapping[i],deleted_alias=i in aliases)
                          for i in range(len(old))],
        aliases=[dict(deleted_parent=i,retained_parent=j,child=mapping[i],
            old_row=old[i],earlier_definition=old[old[i][1]],
            identity='(1+x)-1=x') for i,j in aliases.items()],
        all_named_registers_remapped=True,domain='every commutative ring'))
    files['SOURCE_PINS.json'] = encoded(dict(archive_path=str(ARCHIVE.relative_to(REPO)),
        archive_sha256=ARCHIVE_SHA,component_prefix=PREFIX,
        all104_component_members={name:digest(blob) for name,blob in sorted(component.items())},
        parent_equation_sha256=PARENT_SHA,
        note='All104 raw component members authenticated in the retained archive. Selected ordinary proof/review sources and all six complete coefficient payloads copied here. No formal proof source is edited or compiled.'))
    files['PROVENANCE.json'] = encoded(dict(archive_sha256=ARCHIVE_SHA,parent_equation_sha256=PARENT_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),
        oracle_sha256=digest(files['source/independent_norm_oracle.py']),
        semantic_relation='Exact pointwise full-polynomial identity with the147-operation parent for every integer input and coefficient value.',
        native_boundary='Inherits the reviewed original signed source34/native compiler/calibration theorem; no new compiler, Lean or internal-ZFC claim.'))
    files['BUILD.json'] = encoded(dict(status='PASS',integer_variables=14,operations=145,
        operation_counts=child['operation_counts'],exact_degree=568,norm_degree=512,
        sha256={name:digest(blob) for name,blob in files.items()}))
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
    print(json.dumps(dict(status='PASS',check=args.check,integer_variables=14,
                          operations=145,exact_degree=568),indent=2))


if __name__ == '__main__':
    main()
