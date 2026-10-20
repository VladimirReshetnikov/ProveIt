#!/usr/bin/env python3
"""Independent source/schema comparison for the rho6(a,b) alternative seed.
This is not a full candidate-specific binary runtime proof.
"""
from pathlib import Path
from functools import cache
import sys,json,hashlib
P=Path('research_sub223/portable222');sys.path.insert(0,str(P));import source_language as s
sys.path.insert(0,str(P/'verification'));from check_combined_emitter import postfix
oldfile=Path('research_sub222/delivery/K221_Construction_2026-10-20/machine/sites221.json');newfile=Path('research_sub221/calculus/row_renamings/r6_acb/sites.json')
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
@cache
def flat(t):return(t,)if s.leaf(t)else flat(t[0])+flat(t[1])
I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);N=lambda a:I(a,1)
old=I(N(Q('a',N(Q('a','c')))),'c');new=I(N(Q('a',N(Q('a','b')))),'b')
def subst(t,m):return(t[0],subst(t[1],m),subst(t[2],m))if isinstance(t,tuple)else m.get(t,t)
assert subst(new,dict(a='a',b='c',c='b'))==old
assert subst(old,dict(a='a',b='c',c='b'))==new
mac={int(k):freeze(v)for k,v in json.load(open(P/'verification/macro_data.json'))['macros'].items()}
def prog(f):
 nodes=[mac[m]for m in postfix(f)];t=nodes[-1]
 for n in reversed(nodes[:-1]):t=n,t
 assert s.boundary(t)==(0,0,False)
 return t
oldprog,newprog=prog(old),prog(new);ot=s.tree(json.load(open(oldfile)));nt=s.tree(json.load(open(newfile)));of,nf=flat(ot),flat(nt)
assert of[895:1178]==flat(oldprog)
assert nf==of[:895]+flat(newprog)+of[1178:]
assert len(of)==len(nf)==4744
og,_=s.graph_arithmetic(s.sites(ot));ng,checks=s.graph_arithmetic(s.sites(nt));assert og==s.graph_intervals(s.sites(ot))and ng==s.graph_intervals(s.sites(nt))
assert all(a[1]==b[1]for a,b in zip(og,ng))
# Macro contracts are inherited; this comparison binds all changed instructions
# to the literal parameter-copy substitution, not merely a few numeric samples.
receipt=dict(status='ALL_PARAMETER_RHO6_SCHEMA_AND_LITERAL_EMITTER_COMPARISON_PASS',source_sha256=hashlib.sha256(newfile.read_bytes()).hexdigest(),old_formula=old,new_formula=new,surjective_parameter_bijection={'a':'a','b':'c','c':'b'},changed_primitive_interval=[895,1178],all_other_primitives_equal=True,all_guarded_control_targets_equal=True,independent_cfg_resolvers_agree=True,arithmetic_checks=checks,metrics=s.metrics(nt),scope='Alternative221 research seed only. Same globally enumerated axiom schema; candidate-specific binary unbounded runtime and startup are not certified here.')
Path('research_sub221/calculus/r6_parameter_seed_certificate.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
