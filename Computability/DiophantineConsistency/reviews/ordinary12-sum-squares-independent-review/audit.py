#!/usr/bin/env python3
"""Independent source/artifact and degree audit of the 94-gate model bridge."""
from pathlib import Path
from hashlib import sha256
import gzip
import json
import os
import re

H = Path(__file__).resolve().parent
D = H.parents[1]
R = D / 'research'
C = R / 'ordinary12-sum-of-squares-candidate'
M = R / 'ordinary12-sum-squares-model-bridge'
F = R / 'ordinary12-ipra-bridge/free-j-prototype/Ordinary12FreeJ.lean'
FB = R / 'ordinary12-ipra-bridge/free-j-completeness-factor-bridge-prototype/FreeJCompletenessFactorBridge.lean'
BM = R / 'ordinary12-ipra-bridge/compact44-byte-ports-model-iff-prototype/observations/prepare-attempt01/manifest.json'
SUP = D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
pins = {
    C/'candidate.json': 'dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee',
    C/'FreeJSumSquares.lean': '77f22764b45732e2f7b837bf98caf40e6563c232f48ba682c421889b396b7794',
    M/'SumSquaresModelIff.lean': '256b9f9d5202b3d1d7d10116467c5b1aa4351e0eb125d0ffc8fd918911ec67c5',
    F: '542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a',
    FB: 'ecb2c61425fb0307caf925d55d743096938373cba4c368f426d8ff5071d10131',
    C/'observations/attempt03/terminal.json': 'a2d1c86c49776e439b74a3cb929907ee15c2a77ed7c6f1afc0642fb9a63f0913',
    M/'observations/attempt01/terminal.json': 'febe3f4317dd62fa24d0194844490350f08db1176705a6ebf6db08119efba580',
    BM: 'd45af4289b21b8d4f18a4eab385d8a39bfe6d4d2690a59fe7cc1c5f83f818abe',
    SUP/'circuits/positive12_95_degree70.json': '2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22',
    SUP/'coefficients/BINDING.json': 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
}

def sha(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file(), 'dangling/nonfile '+str(path))
    return {'sha256': sha(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def check_records(records):
    for path, expected in records.items():
        need(record(path) == expected, 'record drift: '+path)

for path, expected in pins.items():
    need(sha(path) == expected, 'pinned source drift: '+str(path))
parent = json.loads((SUP/'circuits/positive12_95_degree70.json').read_text())
candidate = json.loads((C/'candidate.json').read_text())
rows = candidate['source']
need(len(rows) == 94 and rows[:89] == parent['source'][:89], 'prefix/count')
need(rows[-5:] == [['A0sq','*','A0','A0'], ['A1sq','*','A1','A1'],
                  ['Nsq','*','N','N'], ['sum01','+','A0sq','A1sq'], ['P12','+','sum01','Nsq']], 'square tail')
need(parent['source'][-6:] == [['g94','+',1,'A0'],['g95','+',1,'A1'],['g96','*','g94','g95'],
                              ['g97','+',1,'N'],['g98','*','g96','g97'],['P12','-','g98',1]], 'parent tail')
need(candidate['witnesses'] == parent['witnesses'] and len(candidate['witnesses']) == 12 and
     candidate['fixed_numerals'] == parent['fixed_numerals'] == ['beta','K0','MC','MF'], 'inputs')
seen = set(candidate['witnesses'] + candidate['fixed_numerals']) | set(range(5))
dependency = {}
for name, op, a, b in rows:
    need(name not in seen and a in seen and b in seen and op in ('+','-','*'), 'DAG row '+name)
    seen.add(name)
    dependency[name] = (a,b)
live, todo = set(), ['P12']
while todo:
    n = todo.pop()
    if n in dependency and n not in live:
        live.add(n)
        todo.extend(dependency[n])
need(len(live) == len(rows) == 94, 'not all 94 gates are live')
counts = {op: sum(row[1] == op for row in rows) for op in ('*','+','-')}
need(counts == {'*':53,'+':24,'-':17}, 'operation breakdown')

# Independently parse the complete source graph and typed witness/port indices.
src = F.read_text()
need(src.count('-- BEGIN LITERAL GRAPH') == src.count('-- END LITERAL GRAPH') == 1, 'graph delimiters')
inside = src.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
parsed = []
for line in inside.splitlines():
    if not line.strip():
        continue
    m = re.fullmatch(r'\s*let (\w+) := (\w+) ([+*\-]) (\w+)\s*',line)
    need(m is not None, 'unparsed Lean graph row: '+line)
    name, a, op, b = m.groups()
    parsed.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
need(parsed == parent['source'], 'full Lean 95 graph differs')
for i, name in enumerate(candidate['witnesses']):
    need(f'let {name} : Expr (Fin 12) := .var {i}' in src, 'witness '+name)
for i, name in enumerate(candidate['fixed_numerals']):
    need(f'let {name} : Expr (Fin 12) := .constant (p {i})' in src, 'port '+name)
fields = re.search(r'structure Core where\n(.*?)\n\nset_option',src,re.S)
need(fields is not None and re.findall(r'^  (\w+) :',fields.group(1),re.M)[:4] == ['first','main','ordinary','output'], 'Core field order')
need('⟨g94,g95,g97,P12,qm,Z,g41,U,a,c,Dstar,polarA,den,polarT,polarCy⟩' in src, 'Core constructor')
bridge = (C/'FreeJSumSquares.lean').read_text()
for snippet in ('| .add _ b => b','rightAdd (core p).first','rightAdd (core p).main',
                'rightAdd (core p).ordinary','a*a + b*b + c*c',
                'FreeJCompletenessFactorBridge.zero_iff_factor_units',
                'first_decompose, main_decompose, ordinary_decompose',
                'rw [internalZero_iff, internalZero_iff, internalZero_iff, internalZero_iff]',
                'mul_self_eq_zero.mp ha0'):
    need(snippet in bridge, 'missing square bridge interface '+snippet)
factor = FB.read_text()
need('theorem zero_iff_factor_units' in factor and 'literal_factor_units p v' in factor and
     'zero_of_factor_units p v h1 h2 h3' in factor, 'factor iff interfaces')
model = (M/'SumSquaresModelIff.lean').read_text()
for snippet in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]',
                'InternalZero (squareLiteral p) v', '∀ j, 0 < v j',
                'InternalZero (positiveShift (squareLiteral byteP)) x',
                'ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0',
                'rw [internalZero_positiveShift, internalZero_positiveShift, retained_eq_literal]',
                'exact zero_iff_literal byteP _', 'simpa only [byteP_eq]'):
    need(snippet in model, 'model interface '+snippet)

# Algebraic upper degree: h=(V+n)^2-1-Q*n*(2*V+n).  Independently
# expand both expressions as sparse Z[Q,V,n] polynomials.
def plus(a,b):
    result = dict(a)
    for monomial, value in b.items():
        result[monomial] = result.get(monomial,0) + value
    return {k:v for k,v in result.items() if v}
def neg(a): return {k:-v for k,v in a.items()}
def times(a,b):
    result = {}
    for ex,x in a.items():
        for ey,y in b.items():
            k = tuple(i+j for i,j in zip(ex,ey))
            result[k] = result.get(k,0) + x*y
    return {k:v for k,v in result.items() if v}
one={(0,0,0):1};q={(1,0,0):1};v={(0,1,0):1};n={(0,0,1):1}
vn=plus(v,n)
lhs=plus(times(plus(one,neg(q)),times(vn,vn)),plus(times(q,times(v,v)),neg(one)))
rhs=plus(plus(times(vn,vn),neg(one)),neg(times(times(q,n),plus(plus(v,v),n))))
need(lhs == rhs == {(0,2,0):1,(0,1,1):2,(0,0,2):1,(0,0,0):-1,(1,1,1):-2,(1,0,2):-1}, 'h cancellation')
lookup={r[0]:r[1:] for r in rows}
for key, val in {'vn':['+','V','n'],'vn2':['*','vn','vn'], 'polarV2':['*','V','V'],
                 'polarQV2':['*','Q','polarV2'],'polarCy':['-','polarQV2',1],
                 'oneQ':['-',1,'Q'],'polarHpart':['*','oneQ','vn2'],
                 'h':['+','polarHpart','polarCy']}.items():
    need(lookup[key] == val,'h graph '+key)
degrees={name:1 for name in candidate['witnesses']}
degrees.update({name:0 for name in candidate['fixed_numerals']})
degrees.update({i:0 for i in range(5)})
syntactic=degrees.copy()
for name, op, a, b in rows:
    syntactic[name] = syntactic[a]+syntactic[b] if op == '*' else max(syntactic[a],syntactic[b])
    degrees[name] = degrees[a]+degrees[b] if op == '*' else max(degrees[a],degrees[b])
    if name == 'h':
        need(degrees['Q'] <= 6 and degrees['V'] <= 6 and degrees['n'] == 1, 'degree premises')
        degrees[name] = max(2*max(degrees['V'],degrees['n']),
                            degrees['Q']+degrees['n']+max(degrees['V'],degrees['n']))
need(syntactic['P12'] == 104 and degrees['P12'] == 84 and
     degrees['A0'] <= 16 and degrees['A1'] <= 14 and degrees['N'] <= 42, 'degree upper')

# Lower degree independently evaluates the DAG as sparse univariate polynomials
# after witness i -> (i+2)t, with the four actual pinned coefficients mod p.
prime = 1000000007
binding=json.loads((SUP/'coefficients/BINDING.json').read_text())
values={name:{1:i+2} for i,name in enumerate(candidate['witnesses'])}
values.update({i:{0:i} for i in range(5)})
payload_pins={}
for name in candidate['fixed_numerals']:
    meta=binding['ports'][name]
    zipped=(SUP/'coefficients'/meta['file']).read_bytes()
    need(sha256(zipped).hexdigest() == meta['sha256_gzip'], 'gzip '+name)
    raw=gzip.decompress(zipped)
    need(sha256(raw).hexdigest() == meta['sha256_raw'] and len(raw) == meta['raw_bytes'], 'raw '+name)
    payload_pins[name]={'compressed':meta['sha256_gzip'],'raw':meta['sha256_raw']}
    values[name]={0:int.from_bytes(raw,'little') % prime}
for name, op, a, b in rows:
    A,B=values[a],values[b]
    out={}
    if op == '*':
        for i,x in A.items():
            for j,y in B.items():
                out[i+j]=(out.get(i+j,0)+x*y)%prime
    else:
        for k in A.keys() | B.keys():
            out[k]=(A.get(k,0)+(1 if op == '+' else -1)*B.get(k,0))%prime
    values[name]={k:x for k,x in out.items() if x}
degree=max(values['P12'])
need(degree == 84 and values['P12'][degree] == 436671052, 'independent modular degree witness')

sq=json.loads((C/'observations/attempt03/terminal.json').read_text())
md=json.loads((M/'observations/attempt01/terminal.json').read_text())
for packet, source, logs in ((sq,C/'FreeJSumSquares.lean',C/'observations/attempt03/compile.log'),
                             (md,M/'SumSquaresModelIff.lean',M/'observations/attempt01/compile.log')):
    need(packet['exit_code'] == 0 and packet['guards_unchanged'] and
         packet['source_sha256'] == packet['workspace_source_sha256_after'] == sha(source) and
         packet['log_sha256'] == sha(logs) and sha(packet['command'][-1]) == packet['object_sha256'], 'compiler receipt')
    log=logs.read_text()
    need(not any(word in log for word in ('error:','warning:','sorryAx')), 'compiler diagnostics')
    reports=re.findall(r'depends on axioms: \[([^\]]*)\]',log,re.S)
    expected=1 if packet is sq else 3
    need(len(reports)==expected and all(re.sub(r'\s+','',r)=='propext,Classical.choice,Quot.sound' for r in reports), 'axiom reports')
check_records(sq['guards_before']);check_records(sq['provider_before']);check_records(md['direct_guards'])
need(sq['provider_unchanged'] and md['union_unchanged'] and md['prior_overlap_count'] == 167, 'provider flags')
union_root=Path(md['command'][-1]).parent/'lib'
actual={p.relative_to(union_root).as_posix():record(p) for p in union_root.rglob('*') if p.is_file()}
need(actual == md['union'] and len(actual)==1288, 'model union inventory')
base=json.loads(BM.read_text())
for key in ('model_before','model_guards','byte_guards'):
    check_records(base[key])
for key, rec in sq['provider_before'].items():
    roots=[Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib'),
           Path('/tmp/ipra-freej-power-finish-pair-01/author/lib')]
    hits=[Path(key).relative_to(root).as_posix() for root in roots if Path(key).is_relative_to(root)]
    need(len(hits)==1 and hits[0] in base['files'] and base['files'][hits[0]]['sha256']==rec['sha256'], 'square provider overlap')
need(len(sq['provider_before'])==167, 'provider overlap count')
for path, expected in pins.items():
    need(sha(path)==expected, 'postcheck source drift: '+str(path))
check_records(sq['guards_before']);check_records(sq['provider_before']);check_records(md['direct_guards'])
need({p.relative_to(union_root).as_posix():record(p) for p in union_root.rglob('*') if p.is_file()} == actual, 'union postcheck drift')
print(json.dumps({'status':'PASS_SCOPED_SOURCE_ARTIFACT_ARITHMETIC_REVIEW',
  'source_pins':{str(p):h for p,h in pins.items()}, 'operation_count':len(rows),'live_count':len(live),
  'operation_breakdown':counts, 'syntactic_upper':syntactic['P12'],'cancellation_upper':degrees['P12'],
  'degree_witness':{'prime':prime,'substitution':'witness i -> (i+2)*t','degree':degree,'leading':values['P12'][degree]},
  'payload_pins':payload_pins,'square_guards':len(sq['guards_before']),'square_provider_records':len(sq['provider_before']),
  'model_direct_guards':len(md['direct_guards']),'selected_model_union':len(actual),'prior_overlap':167,
  'scope':'No fresh Lean replay; no full ancestry, filesystem/JSON/PDF theorem, or compact iPRA derivation.'},indent=2,sort_keys=True))
