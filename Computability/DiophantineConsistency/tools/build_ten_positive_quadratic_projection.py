#!/usr/bin/env python3
"""Build the separate106-operation three-root/quadratic-projection endpoint."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT/'candidates/ten-positive-scaled-norm-reuse'
OUT = ROOT/'candidates/ten-positive-quadratic-projection'
PARENT_SHA = 'b53f25dc8f5e8430cd2c1bece0c396cc315412092d6a3142db8d4882011f0060'
DELETED = {'Dpc2', 'Dmain', 'P2', 'dP2', 'fd', 'HnX'}
NEW_PROJECTION = [
    ['2apc', '*', 2, 'apc'],
    ['X2apc', '+', 'X', '2apc'],
    ['Kquad0', '*', 'X', 'X2apc'],
    ['Kquad', '-', 'Kquad0', 1],
]
NORM8 = [
    ['ab', '+', 'fa', 'fb'],
    ['sig1', '+', 'ab', 'fc'],
    ['aXb', '*', 'fa', 'fb'],
    ['abXc', '*', 'ab', 'fc'],
    ['sig2', '+', 'aXb', 'abXc'],
    ['sig3', '*', 'aXb', 'fc'],
    ['Po', '-', 'fs', 'sig1'],
    ['Po2', '*', 'Po', 'Po'],
    ['4sig2', '*', 4, 'sig2'],
    ['Pe', '-', 'Po2', '4sig2'],
    ['Pe2', '*', 'Pe', 'Pe'],
    ['s3s', '*', 'sig3', 'fs'],
    ['64s3s', '*', 64, 's3s'],
    ['N', '-', 'Pe2', '64s3s'],
]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()


def build():
    files = {}
    raw = (PARENT/'equation.json').read_bytes()
    need(digest(raw) == PARENT_SHA, 'complete frozen122-operation parent')
    parent = json.loads(raw)
    files['source/parent-equation.json'] = raw
    for target, source in (
        ('parent-proof.md', 'README.md'),
        ('parent-check.json', 'CHECK.json'),
        ('parent-check-optimized.json', 'CHECK_OPTIMIZED.json'),
        ('parent-provenance.json', 'PROVENANCE.json'),
        ('original-proof.md', 'source/original-proof.md'),
        ('original-peer.md', 'source/original-peer.md'),
        ('original-replays.json', 'source/original-replays.json'),
        ('independent_norm_oracle.py', 'source/independent_norm_oracle.py'),
    ):
        files['source/'+target] = (PARENT/source).read_bytes()
    for target, source in (
        ('proof-peer.md', 'ten-positive-quadratic-consistency-peer.md'),
        ('proof-peer.py', 'ten-positive-quadratic-consistency-peer.py'),
        ('proof-peer.json', 'ten-positive-quadratic-consistency-peer.json'),
        ('proof-peer-optimized.json', 'ten-positive-quadratic-consistency-peer_OPTIMIZED.json'),
    ):
        files['source/'+target] = (ROOT/'reviews'/source).read_bytes()
    old = parent['source']
    start = next(i for i, row in enumerate(old) if row[0] == 'ab')
    need(start == 94 and len(old[start:]) == 28, 'complete old prefix/norm boundary')
    rows, remap, deleted = [], [], []
    for i, row in enumerate(old[:start]):
        name = row[0]
        if name in DELETED:
            deleted.append(dict(parent_index=i, row=row))
            continue
        if name == 'lin':
            need(row == ['lin', '+', 'HnX', 'apc'], 'exact old projection cut')
            rows.extend(deepcopy(NEW_PROJECTION))
            new_row = ['lin', '+', 'Hn', 'Kquad']
        else:
            new_row = deepcopy(row)
        remap.append(dict(parent_index=i, child_index=len(rows), register=name,
                          definition_copied=row == new_row))
        rows.append(new_row)
    prefix_len = len(rows)
    need({r['row'][0] for r in deleted} == DELETED, 'all six deleted prefix gates')
    rows.extend(deepcopy(NORM8))
    child = deepcopy(parent)
    child['name'] = 'p10_positive_quadratic_projection_degree408'
    child['parent_sha256'] = PARENT_SHA
    child['source'] = rows
    child['operations'] = len(rows)
    child['operation_breakdown'] = dict(Counter(row[1] for row in rows))
    degrees = {name:1 for name in child['witnesses']} | {name:0 for name in child['fixed_numerals']}
    for name, op, a, b in rows:
        da, db = (0 if type(x) is int else degrees[x] for x in (a, b))
        degrees[name] = da+db if op == '*' else max(da, db)
    child['register_degrees'] = {name:degrees[name] for name in parent['register_degrees']
                                  if name in degrees and name not in DELETED}
    child['register_degrees']['Kquad'] = degrees['Kquad']
    child['syntactic_degree'] = degrees['N']
    child['exact_degree'] = 408
    child['proof_status'] = ('Ordinary positive-zero-existence equivalence with frozen122-operation parent; '
        'main Pell classification recovered from strong+auxiliary equations, quadratic projection resolved '
        'by a whole-product Archimedean bound. Not a pointwise polynomial identity; no new Lean/internal-ZFC proof.')
    need(len(rows) == 106 and prefix_len == 92, 'actual106 gates and92-prefix')
    need(child['operation_breakdown'] == {'*':62, '+':26, '-':18}, 'actual complete operation census')
    need(degrees['N'] == 464, 'actual syntactic degree464')
    files['equation.json'] = encoded(child)
    files['DISPLAY_BINDING.json'] = encoded(dict(
        schema='literal_display_binding_snapshot_v1',
        equation_sha256=digest(files['equation.json']),
        proof_sha256=digest((OUT/'PROOF.md').read_bytes()),
        literal_registers=rows,
        display_aliases=dict(A='Am1 (the proof A-prime minus1)', H='Hp',
            Delta='Dp', M='Mtot', Z='Znum', S='fs', Kquad='Kquad',
            native_K='K0 (not Kquad)'),
        projection_definition='Kquad=X*(X+2*apc)-1, with apc=(A-1)*c in the existing page convention A=Am1.',
        normalized_center='Z/M=n+V+Kquad/H+Y/q^3-W*Bt/(q-1)-e/mu^2',
        parent122_alias_binding=dict(literal='bJ=beta*J', equality='q-1=bJ',
            premise='q=bJ+1', occurrences=['G1','qm1L','P1','qm1Y'],
            identity_scope='every commutative ring'),
        norm_arguments=['fs','fa','fb','fc'], norm_rows=NORM8,
        scope='Complete literal formula snapshot for a future renderer. It does not certify an as-yet-unwritten PDF/TeX.'))
    files['PREFIX_REMAP.json'] = encoded(dict(
        schema='complete_projection_and_norm_replacement_v1', parent_sha256=PARENT_SHA,
        unchanged_witnesses=True, unchanged_fixed_tuple=True,
        parent_prefix_length=start, child_prefix_length=prefix_len,
        retained_prefix=remap, deleted_prefix=deleted,
        new_projection=NEW_PROJECTION,
        replaced_projection=dict(parent=['lin', '+', 'HnX', 'apc'], child=['lin', '+', 'Hn', 'Kquad']),
        replaced_tail=dict(parent_indices=list(range(start, len(old))),
                           child_indices=list(range(prefix_len, len(rows))), child_rows=NORM8),
        semantic_scope='Copied gate definitions may receive changed projection inputs; only unaffected registers have equal values. Positive-zero existence equivalence is PROOF.md, not a ring identity of full outputs.'))
    for name, pin in parent['coefficient_binding']['ports'].items():
        blob = (PARENT/'coefficients'/pin['file']).read_bytes()
        need(digest(blob) == pin['gzip_sha256'], 'whole actual coefficient '+name)
        files['coefficients/'+pin['file']] = blob
    files['coefficients/BINDING.json'] = encoded(parent['coefficient_binding'])
    files['PROVENANCE.json'] = encoded(dict(
        parent_path=str(PARENT.relative_to(ROOT)), parent_equation_sha256=PARENT_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),
        oracle_sha256=digest(files['source/independent_norm_oracle.py']),
        fixed_port_hypotheses=['beta odd and beta>=11', '0<MC<beta<MF<2*beta', 'K0>0'],
        mathematical_relation='Equivalence of existence of strictly positive zeros, with explicit witness constructions; not equality of the two polynomials.',
        fixed_tuple='Same complete original compact44 tuple. Generic port-box proof also applies to the separately calibrated BFS44page tuple without equating its K with this K.',
        page_policy='Frozen page and earlier candidates untouched; any promotion requires independent ordinary-proof review.'))
    files['BUILD.json'] = encoded(dict(status='PASS', positive_variables=10,
        operations=106, operation_breakdown=child['operation_breakdown'], exact_degree=408,
        syntactic_degree=464, sha256={name:digest(value) for name, value in files.items()}))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, raw in build().items():
        path = OUT/name
        if args.check:
            need(path.read_bytes() == raw, 'byte-identical '+name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(dict(status='PASS', check=args.check, positive_variables=10,
                          operations=106, exact_degree=408), indent=2))


if __name__ == '__main__':
    main()
