#!/usr/bin/env python3
"""Read-only, bounded modular screen; exact positivity certificates, not exact hit validation."""
import hashlib,itertools,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
source=Path('Computability/DiophantineConsistency/research/nine-sharing-sign14-positive74-quadratic-search/search.py')
source_sha='5f1691bc62d13dbe8eea3526bb2076ff198e180bf223ad36f13535febec8e870'
if hashlib.sha256(source.read_bytes()).hexdigest()!=source_sha:raise RuntimeError('quadratic engine drift')
s=source.read_text(); env={'__file__':str(source.resolve())}
exec(compile(s[:s.index('for i,j in itertools.combinations')],str(source),'exec'),env)
P=env['P']; vals=env['vals']; roots=env['roots']; squares=env['squares']; items=env['items']
pool=env['pool']; one=env['one']; inv=env['inv']; node=env['node']; graph=env['graph']; add_trees=env['add_trees']; out=env['out']
# Exact coefficient arithmetic verifies the square-completion identity.
def add(*ps):
    r={}
    for p in ps:
        for m,c in p.items():r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items() if c}
def scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    r={}
    for m,a in p.items():
        for n,b in q.items():
            k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+a*b
    return {m:c for m,c in r.items() if c}
x={(1,0,0):1};y={(0,1,0):1};z={(0,0,1):1}
forms=[]
for b,c,d in itertools.product((-1,0,1),repeat=3):
    a=4-b*b;det=8-2*(b*b+c*c+d*d)+2*b*c*d
    if det<=0:continue
    assert a>0
    Q=add(mul(x,x),mul(y,y),mul(z,z),scale(b,mul(x,y)),scale(c,mul(x,z)),scale(d,mul(y,z)))
    lhs=scale(4*a,Q)
    rhs=add(scale(a,mul(add(scale(2,x),scale(b,y),scale(c,z)),add(scale(2,x),scale(b,y),scale(c,z)))),
            mul(add(scale(a,y),scale(2*d-b*c,z)),add(scale(a,y),scale(2*d-b*c,z))),scale(2*det,mul(z,z)))
    assert lhs==rhs
    forms.append((b,c,d))
assert len(forms)==23 and len(list(itertools.combinations(range(5),3)))==10
assert len(add_trees(tuple(sorted([out[71],squares[3],squares[4]]))))==3
control=tuple((x*x+y*y+z*z)%P for x,y,z in zip(*(vals[roots[i]] for i in range(3))))
assert out[71] in one[control] and len(graph(env['root']))==74
# Reuse the prior search's negative-control circuit: an added (r+1)-1 costs two.
r=roots[0]; control_r=node('sub',node('add',r,'lit:1'),'lit:1'); control_sq=node('mul',control_r,control_r)
control_root=node('add',control_sq,squares[1])
for sq in squares[2:]:control_root=node('add',control_root,sq)
assert len(graph(control_root))==76
stats={'form_tests':0,'matching_recipes':0,'trees_counted':0,'hits_under_74':0,'zero_sample_targets':0};hits=[]
for group in itertools.combinations(range(5),3):
    vectors=[vals[roots[i]] for i in group]
    for b,c,d in forms:
        target=tuple((x*x+y*y+z*z+b*x*y+c*x*z+d*y*z)%P for x,y,z in zip(*vectors));stats['form_tests']+=1
        if any(t==0 for t in target):stats['zero_sample_targets']+=1
        others=[squares[i] for i in range(5) if i not in group]
        def check(q,recipe):
            stats['matching_recipes']+=1
            for final in add_trees(tuple(sorted([q]+others))):
                stats['trees_counted']+=1; count=len(graph(final))
                if count<74:
                    stats['hits_under_74']+=1;hits.append({'group':group,'form':(b,c,d),'recipe':recipe,'live_gates':count})
        for wire in one.get(target,[]):check(wire,['existing',str(wire)])
        for op,u,v in pool.get(target,[]):check(node(op,u,v),[op,str(u),str(v)])
        for wire in items:
            a=vals[wire]
            needs=[('add',tuple((t-v)%P for t,v in zip(target,a))),('sub',tuple((t+v)%P for t,v in zip(target,a))),('rsub',tuple((v-t)%P for t,v in zip(target,a)))]
            if wire in inv:needs.append(('mul',tuple(t*v%P for t,v in zip(target,inv[wire]))))
            for op,w in needs:
                for first,u,v in pool.get(w,[]):
                    tmp=node(first,u,v);q=node('sub',wire,tmp) if op=='rsub' else node(op,tmp,wire)
                    check(q,[op,[first,str(u),str(v)],str(wire)])
        half=tuple(t*pow(2,-1,P)%P for t in target); needs=[('double',half)]
        square_roots=[pow(t,(P+1)//4,P) for t in target]
        if all(q*q%P==t for q,t in zip(square_roots,target)):
            needs += [('square',tuple(q*sgn%P for q,sgn in zip(square_roots,signs))) for signs in itertools.product((1,-1),repeat=3)]
        for tag,w in needs:
            for first,u,v in pool.get(w,[]):
                tmp=node(first,u,v);check(node('add' if tag=='double' else 'mul',tmp,tmp),[tag,[first,str(u),str(v)]])
assert stats['zero_sample_targets']==0
result={'status':'NO_SMALLER_CANDIDATE_IN_STATED_SCREEN' if not hits else 'CANDIDATES_REQUIRE_EXACT_VERIFICATION','baseline_live_gates':74,'controls':{'original_three_square_wire':True,'three_sum_trees':3,'inserted_identity_live_gates':76},'coefficient_forms':len(forms),'residual_triples':10,'exact_square_completion_forms_verified':len(forms),'search_stats':stats,'hits':hits,'modulus':P,'sample_count':3,'sample_seed':0x46BE,'quadratic_engine_sha256':source_sha,'graph_source_sha256':'cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d','scope':'Finite modular screen only; any hit requires exact identity verification; no global minimality or PDF binding claim.'}
print(json.dumps(result,indent=2,sort_keys=True))
