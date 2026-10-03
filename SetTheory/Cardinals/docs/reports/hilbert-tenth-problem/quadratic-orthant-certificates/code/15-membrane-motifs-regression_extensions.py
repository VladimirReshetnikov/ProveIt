"""Additional exact regressions and the one-step population identity.
These are finite checks of stated claims, not formal verification.
"""
from motif_compiler import *
from pathlib import Path
import json
OUT=Path(__file__).parent
stats={}

def population(c): return 1+sum(population(k) for k in c.children)
def predicted(p, inherited=0):
    mode=rules[p.mode].kind if p.mode>=0 else 'idle'
    copies=inherited+int(mode=='divide')
    return (0 if mode=='dissolve' else 2**copies)+sum(predicted(k,copies) for k in p.children)

# Consecutive dissolution promotes a whole updated forest before ancestor copying.
d=7
rules=[Rule('out','l',0,unit(d,1)), Rule('dissolve','q',2,unit(d,3)), Rule('divide','p',4,unit(d,5),unit(d,6))]
leaf=Plan('l',unit(d,0),mode=0)
inner=Plan('q',unit(d,2),(leaf,),mode=1)
outer=Plan('q',unit(d,2),(inner,),mode=1)
p=Plan('skin',(0,)*d,(Plan('p',unit(d,4),(outer,),mode=2),))
packet=make_packet(p,rules)
base=(0,1,0,2,0,0,0); empty=Cfg('l',(0,)*d)
expected=Cfg('skin',(0,)*d,(Cfg('p',add(base,unit(d,5)),(empty,)),Cfg('p',add(base,unit(d,6)),(empty,))))
assert packet['output']==ckey(expected)
assert population(expected)==predicted(p)
stats['nested_dissolution_then_division']=packet['ledger']

# Signed zeros are not natural-domain certificates.
s={'configs':[{'label':'skin','children':[]}], 'transitions':[{'source':0,'children':[],'mode':-1,'targets':[0]}], 'root':0}
eq,vs=compile_schema(s,[],1);w=dict.fromkeys(vs,0)
w.update({'x:0:0':-1,'u:0:0':-1,'y:0:0':-1,'f:0:0':1})
assert all(q.evaluate(w)==0 for _,q in eq)
assert not all(type(z) is int and z>=0 for z in w.values())
stats['natural_domain_is_required']=True

# Equal unlabelled configurations need not have reference-consistent duplicate IDs.
s={'configs':[{'label':'h','children':[]},{'label':'h','children':[]},{'label':'skin','children':[0]},{'label':'skin','children':[1]}], 'transitions':[{'source':0,'children':[],'mode':-1,'targets':[0]},{'source':2,'children':[0],'mode':-1,'targets':[3]}], 'root':1}
eq,vs=compile_schema(s,[],1);w=dict.fromkeys(vs,0)
w.update({'f:0:0':1,'f:1:3':1})
violations=[(name,q.evaluate(w))for name,q in eq if q.evaluate(w)]
assert violations==[('targetchild:1:0:0',-1),('targetchild:1:0:1',1)]
stats['arbitrary_duplicate_catalogue_converse_fails']=violations

# One unchanged schema at several population sizes, including 10001-bit N.
s={'configs':[{'label':'h','children':[]},{'label':'skin','children':[0]},{'label':'skin','children':[0]}], 'transitions':[{'source':0,'children':[],'mode':0,'targets':[0,0]},{'source':1,'children':[0],'mode':-1,'targets':[2]}], 'root':1}
rules=[Rule('divide','h',0,(1,),(1,))]
eq,vs=compile_schema(s,rules,1)
assert(len(vs),len(eq))==(18,30)
for N in (1,2,13,2**10000):
    w=dict.fromkeys(vs,0)
    w.update({'x:0:0':1,'c:1:0':N-1,'c:2:0':2*N-1,'m:1:0':N-1,'f:0:0':2,'f:1:2':1})
    assert all(q.evaluate(w)==0 for _,q in eq)
stats['constant_schema']={'variables':18,'residuals':30,'largest_population_bits':10001}

# Sharp expanded-population bound and exact dense ledger on growing chains.
for D in range(1,11):
    p=Plan('h',(1,),mode=0)
    for _ in range(D-1):p=Plan('h',(1,),(p,),mode=0)
    p=Plan('skin',(0,),(p,));packet=make_packet(p,rules)
    fs,_,_=expanded_oracle(p,rules)
    assert population(fs[0])==predicted(p)==2**(D+1)-1
    assert packet['ledger']['variables']==2*D*D+11*D+5
    assert packet['ledger']['residuals']==8*D*D+15*D+7
stats['sharp_chain_population_and_ledgers_depths']=10

# Many shapes and all local idle/divide/dissolve mode combinations: population
# identity is structural, so here maximality is intentionally not required.
rules=[Rule('divide','h',0,(1,),(1,)),Rule('dissolve','h',0,(1,))]
shapes=[Cfg('h',(1,))]
for _ in range(3):
    prev=shapes[:]
    shapes += [Cfg('h',(1,),(c,)) for c in prev]
# Add a branching shape and mixed-height cousins.
shapes += [Cfg('h',(1,),(Cfg('h',(1,)),Cfg('h',(1,)))),Cfg('h',(1,),(Cfg('h',(1,),(Cfg('h',(1,)),)),Cfg('h',(1,))))]
checked=0
for shape in {ckey(c):c for c in shapes}.values():
    root=Cfg('skin',(0,),(shape,))
    for plan in enumerate_plans(root,rules):
        fs,_,_=expanded_oracle(plan,rules,check=False)
        assert population(fs[0])==predicted(plan)
        assert population(fs[0])<=2**population(root)-1
        checked+=1
stats['mixed_structural_population_checks']=checked

# Old topology controls elementary-only division availability.
rules=[Rule('divide','h',0,(1,0),(1,0),elementary=True),Rule('dissolve','q',1,(0,1))]
p=Plan('skin',(0,0),(Plan('h',(1,0),(Plan('q',(0,1),mode=1),)),))
packet=make_packet(p,rules)
assert packet['output']==ckey(Cfg('skin',(0,0),(Cfg('h',(1,1)),)))
stats['old_topology_elementary_guard']=True
(OUT/'regression_extensions_receipt.json').write_text(json.dumps({'status':'passed','checks':stats},indent=2)+'\n')
print(json.dumps(stats,indent=2))
