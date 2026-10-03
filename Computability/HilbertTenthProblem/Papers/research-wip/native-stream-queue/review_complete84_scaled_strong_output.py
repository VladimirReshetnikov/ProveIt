#!/usr/bin/env python3
"""Independent bounded source audit; no predecessor or author code executes."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

STEM = 'complete84_scaled_strong_output'
PARENT = 'complete85_auxiliary_bezout_projection'
PARENT_PINS = {
    'py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0',
    'json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
    'md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
}
AUTHOR_PINS = {'py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
OLD = {
    'ic2': ['ic2', '*', 'i', 'c2'],
    'ic22': ['ic22', '*', 'ic2', 'ic2'],
    'strong_difference': ['strong_difference', '*', 'A', 'ic22'],
    'R16': ['R16', '*', 'A', 'strong_difference'],
    'norm_strong': ['norm_strong', '-', 'L16', 'strong_difference'],
}
NEW = [
    ['aux_coefficient_root', '*', 'i', 'Ac2'],
    ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
    ['scaled_f_square', '*', 'A', 'L16'],
    ['norm_strong', '-', 'scaled_f_square', 'R16'],
]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def stable(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b

def source_audit(parent, child):
    old = {r[0]: r for r in parent['source']}
    need(parent['exact_degree']==175 and parent['normalized'] is True, 'normalized parent')
    need(child['exact_degree']==187 and child['normalized'] is True, 'normalized child')
    need(all(old.get(k) == v for k, v in OLD.items()), 'old private cone')
    for key in ('free', 'witnesses', 'fixed_numerals', 'ordinary_input', 'output'):
        need(child[key] == parent[key], 'interface '+key)
    need(len(child['witnesses']) == 18, 'witness count')
    for row in parent['source']:
        if row[0] not in OLD:
            need(not set(row[2:]) & {'ic2', 'ic22', 'strong_difference'},
                 'deleted private consumer')
    expected = {k: r for k, r in old.items() if k not in OLD}
    expected.update({r[0]: r for r in NEW})
    expected['polynomial'] = ['polynomial', '-', 'seven_units', 'A']
    rows = child['source']
    need(len(rows) == len(expected) == 84, 'complete count')
    need({r[0]: r for r in rows} == expected, 'entire independent row map')
    done = set(child['free'])
    for name, op, a, b in rows:
        need(name not in done and op in ('+', '-', '*'), 'SSA/opcode')
        need(all(type(x) is int or (type(x) is str and x in done)
                 for x in (a, b)), 'literal/topology')
        done.add(name)
    table = {r[0]: r for r in rows}
    live = set()
    def visit(name):
        if type(name) is int or name in live:
            return
        live.add(name)
        if name in table:
            visit(table[name][2]); visit(table[name][3])
    visit(child['output'])
    need(live == set(table) | set(child['free']), 'complete liveness')
    counts = Counter(r[1] for r in rows)
    need(counts['*'] == 47 and counts['+']+counts['-'] == 37, 'M/A')
    # Literal positivity chain and factor/finalizer interface, not opaque ports.
    required = [
        ['repunit','*','Bm1','Jrep'], ['q','+','repunit',1],
        ['Lbig','*','q','q'], ['n2','*','Lbig','q'],
        ['wn2','*','w','q'], ['sn2','*','s','n2'],
        ['UM','*','wn2','sn2'], ['R12','+','UM','sn2'],
        ['a4','*',4,'R12'], ['a4m5','+','a4',3],
        ['a_square','*','R12','R12'], ['A','+','a_square','a4m5'],
        ['c2','*','R10a','R10a'], ['Ac2','*','A','c2'],
        ['L16','*','f','f'], ['L17','*','R16','aux_square_gap'],
        ['norm_aux','+','L17','aux_y2'],
        ['norm_pair','*','norm_first','norm_main'],
        ['norm_triple','*','norm_pair','norm_input'],
        ['norm_four','*','norm_triple','norm_aux'],
        ['norm_product','*','norm_four','norm_index'],
        ['all_units','*','norm_product','norm_transport'],
        ['seven_units','*','all_units','norm_strong'],
    ]
    need(all(table.get(r[0]) == r for r in required), 'literal identities/finalizer')
    unchanged = sum(expected.get(k) == r for k, r in old.items())
    need(unchanged == 79, 'unchanged rows')
    return dict(M=47, A=37, total=84, unchanged_rows=unchanged,
                live_supplied_ports=len(child['free']), full_source_sha256=sha(stable(rows)))

# Exact sparse coefficient arithmetic at independent, explicitly checked cuts.
def pconst(c):
    return {(): c} if c else {}

def padd(a, b, sign=1):
    out = dict(a)
    for mon, coef in b.items():
        out[mon] = out.get(mon, 0)+sign*coef
        if not out[mon]: del out[mon]
    return out

def pmul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m+n))
            out[key] = out.get(key, 0)+c*d
    return {m: c for m, c in out.items() if c}

def symbolic(source):
    table = {r[0]: r for r in source}
    cuts = ['A','c2','i','L16','aux_square_gap','aux_y2',
            'norm_first','norm_main','norm_input','norm_index','norm_transport']
    memo = {name: {(j,): 1} for j, name in enumerate(cuts)}
    def expand(name):
        if type(name) is int: return pconst(name)
        if name in memo: return memo[name]
        _, op, a, b = table[name]
        a, b = expand(a), expand(b)
        value = pmul(a, b) if op == '*' else padd(a, b, 1 if op == '+' else -1)
        memo[name] = value
        return value
    return expand

def exact_relation(parent, child):
    old, new = symbolic(parent['source']), symbolic(child['source'])
    need(old('R16') == new('R16'), 'auxiliary coefficient equality')
    need(new('norm_strong') == pmul(old('A'), old('norm_strong')), 'scaled factor')
    need(new('norm_aux') == old('norm_aux'), 'auxiliary factor equality')
    a, b = new('polynomial'), pmul(old('A'), old('polynomial'))
    need(a == b, 'entire polynomial identity over Z')
    return dict(identity='F84 = Delta*F85 over every commutative ring',
                independent_cut_ports=11, expanded_output_terms=len(a),
                complete_identity_sha256=sha(stable([[list(m),c] for m,c in sorted(a.items())])))

def evaluate(source, values):
    env = dict(values)
    for name, op, a, b in source:
        x = env[a] if type(a) is str else a
        y = env[b] if type(b) is str else b
        env[name] = x*y if op == '*' else x+y if op == '+' else x-y
    return env

def dense_line(source, values, modulus):
    env = {k: list(v) for k,v in values.items()}
    for name, op, a, b in source:
        x = env[a] if type(a) is str else [a % modulus]
        y = env[b] if type(b) is str else [b % modulus]
        if op == '*':
            v = [0]*(len(x)+len(y)-1)
            for i,c in enumerate(x):
                for j,d in enumerate(y):
                    v[i+j] = (v[i+j]+c*d) % modulus
        else:
            v = [((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*
                  (y[i] if i<len(y) else 0)) % modulus for i in range(max(len(x),len(y)))]
        while len(v)>1 and v[-1]==0: v.pop()
        env[name] = v
    return env

def check_degrees(parent, child):
    bounds = {x: (0 if x in child['fixed_numerals'] else 1) for x in child['free']}
    for name, op, a, b in child['source']:
        da = bounds[a] if type(a) is str else 0
        db = bounds[b] if type(b) is str else 0
        bounds[name] = da+db if op=='*' else max(da,db)
    need(bounds['polynomial']==197 and bounds['A']==12, 'syntactic degree upper')
    rows=[]
    for case,mod in enumerate((1000033,1000037)):
        constants=dict(Bm1=15+16*case,Kconstant=97+case,twice_cell_bits=2+2*case,
                       inner_bits=1+case,MC=7+case,MF=5+case)
        coeff={name:j+11+case for j,name in enumerate(child['free']) if name not in constants}
        line={name:[constants[name]] if name in constants else [0,coeff[name]] for name in child['free']}
        old=dense_line(parent['source'],line,mod)
        new=dense_line(child['source'],line,mod)
        need(len(old['polynomial'])==176 and len(new['polynomial'])==188, 'exact line degrees')
        Q=constants['Bm1']*coeff['Jrep']
        trans=coeff['w']*(Q-coeff['F']-coeff['Z']-coeff['alpha']-constants['twice_cell_bits']*coeff['x'])-coeff['transport_quotient']*Q
        expected=32*pow(Q,111,mod)*coeff['h']*(coeff['rho']+coeff['sigma'])*coeff['delta']**2*coeff['i']**4*(coeff['eta']+coeff['zeta'])**13*coeff['w']**18*coeff['s']**31*trans*coeff['auxiliary_quotient']**2*coeff['f']**2 % mod
        need(new['polynomial'][-1]==expected and expected!=0, 'expanded uniform leader specialization')
        need(new['polynomial'][-1]==old['polynomial'][-1]*old['A'][-1]%mod, 'leading scale')
        rows.append(dict(modulus=mod,degree=187,leading_coefficient=expected,fixed_numerals=constants))
    return dict(exact_degree=187,uniform_upper_from_identity='12+175',gate_upper=197,independent_lines=rows)

def verify(root, author_root):
    need(set(AUTHOR_PINS)=={'py','json','md'}, 'author packet not frozen')
    for ext,pin in PARENT_PINS.items():
        need(sha((root/(PARENT+'.'+ext)).read_bytes())==pin,'parent pin '+ext)
    for ext,pin in AUTHOR_PINS.items():
        need(sha((author_root/(STEM+'.'+ext)).read_bytes())==pin,'author pin '+ext)
    parent=json.loads((root/(PARENT+'.json')).read_text())['packet']
    author=json.loads((author_root/(STEM+'.json')).read_text())
    need(author['source_sha256']==AUTHOR_PINS['py'], 'author source/receipt binding')
    deps={}
    for label in ('parent_pins','inherited_pins'):
        for name,pin in author[label].items():
            need(type(name) is str and not Path(name).is_absolute(), 'dependency path')
            need((root/name).resolve().is_relative_to(root.resolve().parents[1]), 'dependency outside Papers')
            need(name not in deps or deps[name]==pin, 'conflicting dependency pin')
            need(sha((root/name).read_bytes())==pin, 'author dependency '+name)
            deps[name]=pin
    child=author['packet']
    ledger=source_audit(parent,child)
    identity=exact_relation(parent,child)
    numerics=0
    for case in range(40):
        values={x:Fraction(((case+7)*(j+5))%23-11,1 if case<20 else j%5+1) for j,x in enumerate(child['free'])}
        old=evaluate(parent['source'],values);new=evaluate(child['source'],values)
        need(new['polynomial']==old['A']*old['polynomial'], 'complete signed evaluation')
        for name in ('R16','norm_aux','norm_first','norm_main','norm_input','norm_index','norm_transport'):
            need(new[name]==old[name],'unchanged factor value '+name)
        numerics+=1
    return dict(source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,parent_pins=PARENT_PINS,dependency_pins=deps,
                ledger=ledger,identity=identity,degree=check_degrees(parent,child),
                signed_whole_evaluations=numerics,rational_assignments=20,
                scope='Independent complete row map, live ports, coefficient identity and degree; no predecessor/author imports or giant positive Pell witnesses. Positive zero theorem uses Delta>0 on the inherited full interface.')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--author-root',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--expect',type=Path)
    args=ap.parse_args()
    need(not(args.output and args.expect),'choose output or expect')
    result=verify(args.root,args.author_root or args.root)
    if args.expect:
        need(same(result,json.loads(args.expect.read_text())),'exact receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',operations=result['ledger']['total'],degree=result['degree']['exact_degree'],whole_evaluations=result['signed_whole_evaluations'])))

if __name__=='__main__':
    main()
