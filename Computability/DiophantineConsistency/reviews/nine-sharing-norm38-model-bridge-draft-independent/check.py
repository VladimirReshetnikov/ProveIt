#!/usr/bin/env python3
"""Independent polynomial interpretation of an uncompiled assignment draft."""
import hashlib, json, re, sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P = Path(__file__).resolve().parent
D = P.parents[1]
A = D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean'
S = D/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
G = D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A) == 'c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a'
assert sha(S) == '312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
assert sha(G) == 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
assert sha(A.parent/'SharingNormTrace.lean') == '40dda490395ab26ae02652b7af0171593ecf1b736ffd6582bafb277e38d5ffc8'
assert sha(A.parent/'SharingNormSquares.lean') == '926de997e22f6e9a287c36f94b0403b6222e219c9b0d5d16cf34b5f7d30c198c'
source = A.read_text(); seed = json.loads(S.read_text()); graph = json.loads(G.read_text())

def plus(a,b,sign=1):
    z=dict(a)
    for k,v in b.items(): z[k]=z.get(k,0)+sign*v
    return {k:v for k,v in z.items() if v}
def prod(a,b):
    z={}
    for x,u in a.items():
        for y,v in b.items():
            k=tuple(sorted(x+y));z[k]=z.get(k,0)+u*v
    return {k:v for k,v in z.items() if v}
def atom(x): return {(x,):1}
def num(n): return {():n} if n else {}
def parse_json(t):
    if t[0]=='num': return num(t[1])
    if t[0]=='var': return atom('v'+str(t[1]))
    if t[0]=='port': return atom('p'+t[1])
    a,b=map(parse_json,t[1:]);return prod(a,b) if t[0]=='mul' else plus(a,b,1 if t[0]=='add' else -1)
def read_component(s):
    if s.isdigit():return num(int(s))
    if re.fullmatch(r'w \d+',s):return atom('v'+str(int(s[2:])+1))
    if re.fullmatch(r'w \d+ \+ 1',s):return plus(atom('v'+str(int(s.split()[1])+1)),num(1))
    if re.fullmatch(r'ports \d+',s):return atom('p'+graph['fixed_numerals'][int(s.split()[1])])
    raise ValueError(s)
def compute(op,a,b):
    ap,an=a;bp,bn=b
    if op=='add':return plus(ap,bp),plus(an,bn)
    if op=='sub':return plus(ap,bn),plus(an,bp)
    assert op=='mul'
    return plus(prod(ap,bp),prod(an,bn)),plus(prod(ap,bn),prod(an,bp))

assignments=re.findall(r'^  let a(\d+) : SignedPair S := (.+)$',source,re.M)
assert [int(i) for i,_ in assignments] == list(range(81))
values=[]; definitions=[]
for i,(_,rhs) in enumerate(assignments):
    m=re.fullmatch(r'⟨(.+), (.+)⟩',rhs)
    if m: values.append((read_component(m[1]),read_component(m[2])));definitions.append(('pair',))
    else:
        m=re.fullmatch(r'pairCompute GateOp\.(add|sub|mul) a(\d+) a(\d+)',rhs);assert m,rhs
        op,x,y=m[1],int(m[2]),int(m[3]);assert x<i and y<i
        values.append(compute(op,values[x],values[y]));definitions.append((op,x,y))
assert values[:14] == [(plus(atom('v'+str(i+1)),num(1)),{}) for i in range(14)]
assert values[14:18] == [(atom('p'+p),{}) for p in graph['fixed_numerals']]
assert values[18:21] == [(num(n),{}) for n in (1,3,4)]
vector=re.search(r'^  !\[(.*)\]$',source,re.M).group(1).split(', ')
assert vector == ['a'+str(i) for i in range(81)]
gates=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',source)]
assert len(gates)==60
indices={n:i for i,n in enumerate(graph['witnesses'])}
indices.update({p:i+14 for i,p in enumerate(graph['fixed_numerals'])});indices.update({1:18,3:19,4:20})
expected_residuals=[]; terminals={}; terminal_names={'N0','N1','Na','Nt','scaled_Ns'}
for offset,((name,op,a,b),record,(target,left,right,actualop)) in enumerate(zip(graph['source'][:60],seed['gate_records'],gates)):
    tag={'+':'add','-':'sub','*':'mul'}[op]
    assert (target,left,right,actualop)==(offset+21,indices[a],indices[b],tag)
    assert (name,op,a,b)==(record['name'],record['op'],record['left'],record['right'])
    expected=compute(tag,values[left],values[right]); actual=values[target]
    residual_pair=(plus(actual[0],expected[0],-1),plus(actual[1],expected[1],-1))
    if record['kind']=='materialized':
        assert definitions[target]==('pair',)
        expected_residuals.append((name,'positive',residual_pair[0]))
        if 'negative_coordinate' in record:expected_residuals.append((name,'negative',residual_pair[1]))
        else: assert residual_pair[1]=={}
        assert actual[0] == atom('v'+str(record['positive_coordinate']))
        assert actual[1] == (atom('v'+str(record['negative_coordinate'])) if 'negative_coordinate' in record else {})
    else:
        assert definitions[target] == (tag,left,right) and residual_pair == ({},{})
        if name in terminal_names:
            val=plus(actual[0],actual[1],-1)
            rhs=plus(values[indices['Delta']][0],values[indices['Delta']][1],-1) if name=='scaled_Ns' else num(1)
            expected_residuals.append((name,'norm',plus(val,rhs,-1)));terminals[name]=target
    indices[name]=target
assert len(expected_residuals)==29 and len(seed['residuals'])==29
for (name,kind,poly),r in zip(expected_residuals,seed['residuals']):
    assert (name,kind)==(r['gate'],r['kind']) and poly==parse_json(r['expr']), (name,kind)
assert terminals=={'N1':44,'N0':61,'Nt':66,'Na':78,'scaled_Ns':80}
assert indices['Delta']==36
for s in ['(v 61) = 1','(v 44) = 1','(v 78) = 1','(v 66) = 1','(v 80) = pairValue embed (v 36)']:assert s in source
print(json.dumps({'status':'PASS_EXTERNAL_SYMBOLIC_ALIGNMENT_ONLY','assignment_sha256':sha(A),'seed_sha256':sha(S),'graph_sha256':sha(G),'nodes':len(values),'gates':len(gates),'residual_polynomials_compared':len(expected_residuals),'terminals':terminals,'scope':'External symbolic comparison only; no Lean elaboration, model proof, port-cast or endpoint claim.'},indent=2,sort_keys=True))
