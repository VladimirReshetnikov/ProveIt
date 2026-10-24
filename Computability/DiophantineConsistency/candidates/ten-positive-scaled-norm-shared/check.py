#!/usr/bin/env python3
"""Independent complete remap, associativity, literal norm and degree controls."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COMMIT = '8380e70262337360af048a88ebcd9c17b4c7808d'


def need(ok,message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(raw):
    return sha256(raw).hexdigest()


def evaluate(rows,inputs,prime=None):
    env = dict(inputs)
    def val(x):
        return x if type(x) is int else env[x]
    for name,op,a,b in rows:
        u,v = val(a),val(b)
        out = u+v if op == '+' else u-v if op == '-' else u*v
        env[name] = out if prime is None else out % prime
    return env


def line_degree(values,prime):
    order = -1
    leading_difference = None
    values = list(values)
    level = 0
    while values:
        if values[0]:
            order,leading_difference = level,values[0]
        values = [(b-a)%prime for a,b in zip(values,values[1:])]
        level += 1
    return order,leading_difference


def main():
    provenance = load(HERE/'PROVENANCE.json')
    need(provenance['commit'] == COMMIT,'immutable source commit')
    for name,pin in provenance['parent_files'].items():
        raw = (HERE/'source/parent'/name).read_bytes()
        original = subprocess.run(['git','show',COMMIT+':'+provenance['parent_path']+'/'+name],cwd=REPO,capture_output=True,check=True).stdout
        need(raw == original and digest(raw) == pin,'whole original parent file '+name)
    for name,pin in provenance['peer_files'].items():
        raw = (HERE/'source/peer'/name).read_bytes()
        member = 'Computability/DiophantineConsistency/reviews/'+name
        original = subprocess.run(['git','show',provenance['peer_commit']+':'+member],cwd=REPO,capture_output=True,check=True).stdout
        need(raw == original and digest(raw) == pin,'immutable committed independent peer file '+name)
    parent = load(HERE/'source/parent/p10_positive_degree816.json')
    child = load(HERE/'equation.json')
    remap = load(HERE/'PREFIX_REMAP.json')
    need(child['domain'] == parent['domain'] == 'strictly positive integers','unchanged domain')
    need(child['witnesses'] == parent['witnesses'] and len(set(child['witnesses'])) == 10,'complete unchanged witness list')
    need(child['fixed_numerals'] == parent['fixed_numerals'] == ['beta','K0','MC','MF'],'complete unchanged fixed tuple')
    need(child['output'] == parent['output'] == 'N','same final output')
    old,new = parent['source'],child['source']
    deleted = remap['deleted_gate']
    replacement = remap['replaced_gate']
    need(old[deleted['parent_index']] == deleted['row'] == ['Am1I','*','Am1','I'],'exact removed multiplication')
    need(old[replacement['parent_index']] == replacement['old_row'] == ['4Am1I','*',4,'Am1I'],'exact replaced gate')
    need(new[replacement['child_index']] == replacement['new_row'] == ['4Am1I','*','4Am1','I'],'exact shared product')
    need([r for r in old if 'Am1I' in r[2:]] == [replacement['old_row']],'no lost old intermediate use')
    need([r for r in new[:replacement['child_index']] if r[0] == '4Am1'] == [['4Am1','*',4,'Am1']], 'earlier prefix computes the required scalar factor')
    retained = remap['retained_gates']
    need([r['parent_index'] for r in retained] == [i for i in range(len(old)) if i != deleted['parent_index']], 'complete parent coverage')
    need([r['child_index'] for r in retained] == list(range(len(new))), 'complete ordered child coverage')
    for row in retained:
        i,j = row['parent_index'],row['child_index']
        need(old[i][0] == new[j][0] == row['register'],'whole prefix register map')
        need(i == replacement['parent_index'] or old[i] == new[j], 'every other literal gate unchanged')
    # The copied independent peer helper is an exact sparse ring oracle,
    # not an author builder/verifier. Its main() is never invoked here.
    helper_path = HERE/'source/peer/ten-positive-scaled-norm-peer.py'
    need(digest(helper_path.read_bytes()) == provenance['peer_files'][helper_path.name],'independent algebra helper pin')
    spec = importlib.util.spec_from_file_location('independent_sparse_ring_oracle',helper_path)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    u,i = oracle.variable(0),oracle.variable(1)
    need((4*(u*i)).t == ((4*u)*i).t, 'universal associativity cut over Z')
    available = set(child['witnesses']+child['fixed_numerals'])
    degrees = {v:1 for v in child['witnesses']} | {v:0 for v in child['fixed_numerals']}
    dependencies = {}
    for name,op,a,b in new:
        need(name not in available and op in ('+','-','*'),'fresh binary arithmetic gate')
        need(all(type(x) is int or x in available for x in (a,b)),'topological new circuit')
        available.add(name)
        dependencies[name] = (a,b)
        da,db = (0 if type(x) is int else degrees[x] for x in (a,b))
        degrees[name] = da+db if op == '*' else max(da,db)
    live = set()
    todo = ['N']
    while todo:
        x = todo.pop()
        if type(x) is int or x in live:
            continue
        live.add(x)
        todo.extend(dependencies.get(x,()))
    need(live == available,'all gates, unknowns and ports live')
    counts = Counter(r[1] for r in new)
    need(len(new) == child['operations'] == 123 and dict(counts) == child['operation_breakdown'] == {'*':73,'+':30,'-':20},'123 live arithmetic operations')
    need(degrees['N'] == child['syntactic_degree'] == parent['syntactic_degree'] == 928,'unchanged syntactic degree')
    need(all(degrees[name] == degree for name,degree in child['register_degrees'].items()),'every stated degree contract')
    x,a,b,c,d,omega = [oracle.variable(j) for j in range(6)]
    start = next(j for j,r in enumerate(new) if r[0] == 'ab')
    tail = new[start:]
    norm = oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=c,fd=d))['N']
    need(len(tail) == 28 and norm.t == oracle.norm_oracle(x,[a,b,c,d]).t, 'complete unchanged universal16-fold norm')
    centered = oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega,fd=d))['N']
    weights = (58,78,84,0,64,102)
    weighted = {m:sum(e*w for e,w in zip(m,weights)) for m in centered.t}
    top = {m:centered.t[m] for m,w in weighted.items() if w == max(weighted.values())}
    need(max(weighted.values()) == 816 and top == {(0,0,0,0,0,8):1},'exact centered weight certificate')
    coefficients = {}
    for name,pin in child['coefficient_binding']['ports'].items():
        need(pin == parent['coefficient_binding']['ports'][name],'original whole fixed-port recipe')
        blob = (HERE/'coefficients'/pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'],'authentic complete fixed payload')
        coefficients[name] = int.from_bytes(raw,'little')
        need(coefficients[name].bit_length() == pin['bits'],'fixed payload width')
    need(coefficients['beta'] == 2**590069-1 > 0,'actual nonzero beta')
    rng = random.Random(123816)
    diagnostics = 0
    for prime in (1009,(1<<127)-1):
        for _ in range(50):
            inputs = {name:rng.randrange(-20,21) for name in child['witnesses']}
            inputs.update({name:value%prime for name,value in coefficients.items()})
            want,have = evaluate(old,inputs,prime),evaluate(new,inputs,prime)
            need(want['N'] == have['N'] and all(want[r['register']] == have[r['register']] for r in retained),'every retained gate value unchanged')
            diagnostics += 1
    # Actual-tuple degree attainment on two complete circuit lines. The
    # inherited nonzero omega0 proof supplies the unbounded exact-degree claim.
    slices = []
    for prime in ((1<<127)-1,(1<<89)-1):
        direction = {name:rng.randrange(1,prime) for name in child['witnesses']}
        base = {name:rng.randrange(1,prime) for name in child['witnesses']}
        inputs = {name:value%prime for name,value in coefficients.items()}
        values = []
        for t in range(930):
            env = inputs | {name:(base[name]+t*direction[name])%prime for name in child['witnesses']}
            values.append(evaluate(new,env,prime)['N'])
        degree,_ = line_degree(values,prime)
        need(degree == 816,'complete actual-tuple line attains exact degree816')
        slices.append(dict(prime_bits=prime.bit_length(),degree=degree))
    corrupt = deepcopy(replacement['new_row'])
    corrupt[2] = 'Am1'
    bad_value = evaluate([corrupt],{'Am1':u,'I':i,'4Am1':4*u})['4Am1I']
    need(bad_value.t != (4*(u*i)).t,'missing factor4 corruption rejected by local identity')
    for name,pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/name).read_bytes()) == pin,'generated artifact seal')
    parent_replays = load(HERE/'source/peer/ten-positive-scaled-norm-peer.json')
    need(parent_replays['status'] == 'PASS' and all(r['exit_code'] == 0 for r in parent_replays['replays']), 'full inherited parent replay receipts')
    report = dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,
        operations=123,operation_breakdown=dict(counts),exact_degree=816,syntactic_degree=928,
        full_remapped_gates=len(retained),removed_gate='Am1I',generic_associativity_identity=True,
        universal_norm_terms=len(norm.t),centered_norm_terms=len(centered.t),unique_weight816_term='omega^8',
        every_retained_gate_diagnostics=diagnostics,actual_tuple_degree_slices=slices,
        corrupted_cut_rejected=True,equation_sha256=digest((HERE/'equation.json').read_bytes()),
        scope='Exact pointwise complete polynomial identity, every gate remapped, whole fixed tuple, independent16-fold norm/weighted degree and actual degree controls. Ordinary equivalence inherited unchanged; no new internal object-ZFC proof or Lean.')
    output = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE/output).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
