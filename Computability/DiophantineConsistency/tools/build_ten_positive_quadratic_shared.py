#!/usr/bin/env python3
"""Build the exact105-operation evaluator of the degree408 positive endpoint."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT/'candidates/ten-positive-quadratic-projection'
OUT = ROOT/'candidates/ten-positive-quadratic-projection-shared'
PARENT_SHA = 'a0472d086ac0e0a2058c75e0cc15c6340125dd869c1f16d053609c3331fbffa9'
TAIL = [
    ['U', '+', 'fs', 'fc'],
    ['ab', '+', 'fa', 'fb'],
    ['Po', '-', 'U', 'ab'],
    ['sc', '*', 'fs', 'fc'],
    ['aXb', '*', 'fa', 'fb'],
    ['scab', '+', 'sc', 'aXb'],
    ['4scab', '*', 4, 'scab'],
    ['Po2', '*', 'Po', 'Po'],
    ['Pe', '-', 'Po2', '4scab'],
    ['Pe2', '*', 'Pe', 'Pe'],
    ['scaXb', '*', 'sc', 'aXb'],
    ['64scaXb', '*', 64, 'scaXb'],
    ['N', '-', 'Pe2', '64scaXb'],
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
    need(digest(raw) == PARENT_SHA, 'complete frozen106-operation parent')
    parent = json.loads(raw)
    files['source/parent-equation.json'] = raw
    for target, source in (
        ('parent-proof.md', 'README.md'), ('ordinary-proof.md', 'PROOF.md'),
        ('parent-check.json', 'CHECK.json'), ('parent-check-optimized.json', 'CHECK_OPTIMIZED.json'),
        ('parent-provenance.json', 'PROVENANCE.json'), ('parent-display-binding.json', 'DISPLAY_BINDING.json'),
        ('proof-peer.md', 'source/proof-peer.md'), ('proof-peer.json', 'source/proof-peer.json'),
        ('proof-peer-optimized.json', 'source/proof-peer-optimized.json'),
        ('original-proof.md', 'source/original-proof.md'),
        ('original-peer.md', 'source/original-peer.md'),
        ('original-replays.json', 'source/original-replays.json'),
        ('independent_norm_oracle.py', 'source/independent_norm_oracle.py'),
    ):
        files['source/'+target] = (PARENT/source).read_bytes()
    prefix = deepcopy(parent['source'][:92])
    need(parent['source'][92][0] == 'ab' and len(parent['source'][92:]) == 14,
         'complete parent prefix/tail cut')
    child = deepcopy(parent)
    child['name'] = 'p10_positive_quadratic_projection_shared_degree408'
    child['parent_sha256'] = PARENT_SHA
    child['source'] = prefix+deepcopy(TAIL)
    child['operations'] = len(child['source'])
    child['operation_breakdown'] = dict(Counter(r[1] for r in child['source']))
    child['proof_status'] = ('Exact universal complete-polynomial identity with the frozen106-operation '
        'degree408 parent, by symmetric octic norm refactoring; ordinary positive-zero theorem unchanged. '
        'No new native calibration or Lean/internal-ZFC proof.')
    need(child['operations'] == 105 and child['operation_breakdown'] == {'*':61,'+':26,'-':18},
         'actual105-operation census')
    files['equation.json'] = encoded(child)
    files['PREFIX_REMAP.json'] = encoded(dict(schema='complete_identical_prefix_and_symmetric_tail_v1',
        parent_sha256=PARENT_SHA,
        prefix=[dict(parent_index=i,child_index=i,register=r[0]) for i,r in enumerate(prefix)],
        replaced_tail=dict(parent_indices=list(range(92,106)),child_indices=list(range(92,105)),
                           old_rows=parent['source'][92:],new_rows=TAIL),
        exact_inner_identity='(s-a-b-c)^2-4*(a*b+(a+b)*c)=(s+c-a-b)^2-4*(s*c+a*b)',
        domain='every commutative ring, for every input and fixed-port value'))
    for name, pin in child['coefficient_binding']['ports'].items():
        blob = (PARENT/'coefficients'/pin['file']).read_bytes()
        need(digest(blob) == pin['gzip_sha256'], 'complete fixed coefficient '+name)
        files['coefficients/'+pin['file']] = blob
    files['coefficients/BINDING.json'] = encoded(child['coefficient_binding'])
    old_display = json.loads(files['source/parent-display-binding.json'])
    display = deepcopy(old_display)
    display['equation_sha256'] = digest(files['equation.json'])
    display['literal_registers'] = child['source']
    display['norm_rows'] = TAIL
    display['parent_degree408_equation_sha256'] = PARENT_SHA
    display['norm_formula'] = 'With p=fs+fc-fa-fb, x=fs*fc and y=fa*fb, N=(p^2-4*(x+y))^2-64*x*y.'
    display['scope'] = 'Complete105-gate literal snapshot for future rendering; exact identity with106parent. Does not certify an as-yet-unwritten PDF/TeX.'
    files['DISPLAY_BINDING.json'] = encoded(display)
    files['PROVENANCE.json'] = encoded(dict(parent_path=str(PARENT.relative_to(ROOT)),
        parent_equation_sha256=PARENT_SHA,
        generator_sha256=digest(Path(__file__).read_bytes()),
        oracle_sha256=digest(files['source/independent_norm_oracle.py']),
        ordinary_proof_sha256=digest(files['source/ordinary-proof.md']),
        semantic_relation='Pointwise universal polynomial identity with106parent; fixedtuple, positiveunknowns and degree unchanged.',
        page_policy='Earlier page/PDF/TeX/parents untouched. This snapshot may be used for the pending single significant degree408page update.'))
    files['BUILD.json'] = encoded(dict(status='PASS',positive_variables=10,operations=105,
        operation_breakdown=child['operation_breakdown'],exact_degree=408,syntactic_degree=464,
        sha256={name:digest(value) for name,value in files.items()}))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    for name, raw in build().items():
        path = OUT/name
        if args.check:
            need(path.read_bytes() == raw,'byte-identical '+name)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,
                          operations=105,exact_degree=408),indent=2))


if __name__ == '__main__':
    main()
