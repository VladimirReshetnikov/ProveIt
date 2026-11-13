#!/usr/bin/env python3
"""Reconstruct the incomplete 115 supplement in a temporary directory.

The reconstruction is byte-pinned to the supplement manifest and historical
source commit; this does not prove the inherited ordinary arithmetic theorem.
"""
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BASE = Path('Computability/DiophantineConsistency')
SUP = BASE / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
COEFF = BASE / 'candidates/free-j-polarized-positive/source/positive/coefficients'
ALT = BASE / 'research/saturated-direct-carrier-cse/coefficients/compact44_bfs'
PIN = '84e16e43092614bae262ca59651cb9d77e31a255'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def show(path):
    p = subprocess.run(['git', 'show', f'{PIN}:{path.as_posix()}'], cwd=ROOT,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return p.stdout


def direct_identity(parent, child):
    """Independently verify the complete graph using the displayed Z identity."""
    rows0 = {r[0]: r for r in parent['source']}
    rows1 = {r[0]: r for r in child['source']}
    require(len(rows0) == 96 and len(rows1) == 95, 'row counts')
    require(parent['domain'] == child['domain'] == 'strictly positive integers', 'domain')
    for doc in (parent, child):
        known = set(doc['witnesses'] + doc['fixed_numerals'])
        counts = {'+':0, '-':0, '*':0}
        for name, op, a, b in doc['source']:
            require(name not in known and op in counts, 'fresh binary gate')
            require(all(type(v) is int or v in known for v in (a,b)), 'topological order')
            counts[op] += 1; known.add(name)
        require(doc['operation_breakdown'] == counts, 'operator census')
    expected0 = {'g22': ['g22','*','k','qm'], 'W':['W','+',1,'g22'],
                 'M':['M','*','q3','qm'], 'g32':['g32','*','M','g31'],
                 'g33':['g33','*','Y','qm'], 'g34':['g34','+','g32','g33'],
                 'g35':['g35','*','W','q3'], 'g36':['g36','*','Bt','g35'],
                 'Z':['Z','-','g34','g36']}
    expected1 = {'M':['M','*','q3','qm'],
                 'folded_kBt':['folded_kBt','*','k','Bt'],
                 'folded_g31':['folded_g31','-','g31','folded_kBt'],
                 'g32':['g32','*','M','folded_g31'],
                 'g33':['g33','*','Y','qm'], 'g34':['g34','+','g32','g33'],
                 'folded_q3Bt':['folded_q3Bt','*','q3','Bt'],
                 'Z':['Z','-','g34','folded_q3Bt']}
    require(all(rows0.get(k) == v for k,v in expected0.items()), 'parent cut')
    require(all(rows1.get(k) == v for k,v in expected1.items()), 'child cut')
    # A coefficient collector on the six independent cut variables.
    def add(a,b,sgn=1):
        result = dict(a)
        for m,c in b.items(): result[m] = result.get(m,0) + sgn*c
        return {m:c for m,c in result.items() if c}
    def mul(a,b):
        result = {}
        for m,c in a.items():
            for n,d in b.items():
                key = tuple(sorted(m+n)); result[key] = result.get(key,0)+c*d
        return {m:c for m,c in result.items() if c}
    symbols = {n:{(n,):1} for n in ('q3','qm','k','Bt','g31','Y')}
    def evaluate(rows):
        env = symbols.copy()
        for name,op,a,b in rows:
            if name in env: continue
            a = {():a} if type(a) is int else env[a]
            b = {():b} if type(b) is int else env[b]
            env[name] = mul(a,b) if op == '*' else add(a,b,1 if op == '+' else -1)
        return env['Z']
    require(evaluate(expected0.values()) == evaluate(expected1.values()), 'exact cut identity')
    # All unchanged post-cut nodes must be rooted in shared inputs, the cut,
    # or earlier equal nodes; this also verifies acyclic complete liveness.
    require(parent['witnesses'] == child['witnesses'] and
            parent['fixed_numerals'] == child['fixed_numerals'] and
            parent['output'] == child['output'], 'port and output agreement')
    certified = set(parent['witnesses'] + parent['fixed_numerals'])
    for row in child['source']:
        n,op,a,b = row
        if n == 'Z':
            require(all(x in certified for x in symbols), 'cut boundary certified')
            certified.add(n)
        elif rows0.get(n) == row and all(type(x) is int or x in certified for x in (a,b)):
            certified.add(n)
    require(child['output'] in certified, 'full output transport')
    for doc, rows in ((parent, rows0), (child, rows1)):
        live = set(); todo = [doc['output']]
        while todo:
            n = todo.pop()
            if type(n) is int or n in live: continue
            live.add(n)
            if n in rows: todo.extend(rows[n][2:])
        require(live == set(rows) | set(doc['witnesses']) | set(doc['fixed_numerals']), 'liveness')
    return {'parent_gates':len(rows0),'child_gates':len(rows1),
            'cut_polynomial_terms':len(evaluate(expected1.values())),
            'complete_output_identity':True}


def main():
    supplement = ROOT / SUP
    manifest = json.loads((supplement / 'MANIFEST.json').read_bytes())['files']
    pins = json.loads((supplement / 'SOURCE_PINS.json').read_bytes())
    require(pins['commit'] == PIN, 'source commit')
    source_map = {r['local_path']:Path(r['repository_path']) for r in pins['sources']}
    missing = []
    with tempfile.TemporaryDirectory(prefix='ms115-') as temp:
        destination = Path(temp) / 'supplement'
        shutil.copytree(supplement, destination)
        for name, digest in manifest.items():
            out = destination / name
            if out.exists():
                require(sha(out.read_bytes()) == digest, 'existing manifest mismatch: ' + name)
                continue
            if name in source_map: source = source_map[name]
            elif name.startswith('coefficients/'): source = COEFF / name[len('coefficients/'):]
            else: raise ValueError('no historical source for ' + name)
            data = show(source)
            require(sha(data) == digest, 'historical byte mismatch: ' + name)
            out.parent.mkdir(parents=True, exist_ok=True); out.write_bytes(data)
            missing.append({'target':name,'source':source.as_posix(),'sha256':digest})
        graph = direct_identity(json.loads((destination / 'parents/candidates/free-j-polarized-positive/equation.json').read_bytes()),
                                json.loads((destination / 'circuits/positive12_95_degree70.json').read_bytes()))
        binding = json.loads((destination / 'coefficients/BINDING.json').read_bytes())
        other_binding = json.loads((ROOT / BASE / 'con-zfc-diophantine-forms/98-congruence-certificates/positive/coefficients/BINDING.json').read_bytes())
        comparison = {}
        for name,pin in binding['ports'].items():
            payload = gzip.decompress((destination / 'coefficients' / pin['file']).read_bytes())
            alternate = gzip.decompress((ROOT / ALT / Path(pin['file']).name).read_bytes())
            require(sha(payload) == pin['sha256_raw'], 'raw payload hash')
            require(pin['sha256_raw'] == other_binding['ports'][name]['sha256_raw'], 'manuscript 98 raw binding')
            comparison[name] = {'raw_sha256':sha(payload), 'alternate_raw_sha256':sha(alternate),
                                'same_as_manuscript_98_raw_binding':True,
                                'same_as_alternate_compact44_bfs':payload == alternate}
        require([comparison[n]['same_as_alternate_compact44_bfs'] for n in ('beta','K0','MC','MF')] == [True,False,True,True], 'tuple comparison')
        runs = []
        for flags in ([], ['-O']):
            p = subprocess.run([sys.executable, '-B', *flags, str(destination/'check.py')],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            require(p.returncode == 0, 'reconstructed supplement checker failed: '+p.stderr)
            data = json.loads(p.stdout); require(data['status'] == 'PASS', 'checker status')
            runs.append({'optimized':bool(flags),'exit':p.returncode,
                         'case':next(x for x in data['cases'] if x['name']=='positive12_95_degree70')})
    print(json.dumps({'status':'PASS','source_commit':PIN,'manifest_files':len(manifest),
                      'restored':missing,'independent_graph':graph,
                      'compact44_comparison':comparison,'checker_runs':runs,
                      'scope':'Finite graph, byte identity, and counts only; inherited exact degree, source calibration, ordinary equivalence, and internal iPRA are not proved here.'},indent=2))


if __name__ == '__main__': main()
