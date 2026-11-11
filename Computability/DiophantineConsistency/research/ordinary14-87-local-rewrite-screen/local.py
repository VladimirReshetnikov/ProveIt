#!/usr/bin/env python3
"""Bounded exact-target prefilter for both 87-gate output forms; no Lean."""
import ast,gzip,hashlib,json,random,sys
from itertools import product
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
D=Path(__file__).resolve().parents[2];E=D/'research/p64-qcube79-local-rewrite-search/search.py';G=D/'research/ordinary14-shifted-guard87-probe/candidate.json'
def checked(path,h):raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,path;return raw
tree=ast.parse(checked(E,'4c8e09ecb5ca438123ab0ac1b6cb6e07b5d27f95c6cee651debde2ccbb438f46'));names={'evaluate','live_count','search','alias_and_square_sign'};defs=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names];assert {n.name for n in defs}==names
PRIME=1000000007;SAMPLES=3;SEED=0x8726;exec(compile(ast.Module(body=defs,type_ignores=[]),str(E),'exec'))
assert PRIME%4==3 and all(PRIME%d for d in range(2,int(PRIME**0.5)+1))
g=json.loads(checked(G,'405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'));old=g['source'];out=g['output'];vars=g['witnesses']+g['fixed_numerals'];assert len(old)==live_count(old,out)==87
new=[]
for name,op,a,b in old:
 if name=='Fam':continue
 if name=='Fam2':a=b='Fa'
 if name==out:name='sphere_sum'
 new.append([name,op,a,b])
new.append([out,'-','sphere_sum',1]);assert len(new)==live_count(new,out)==87
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads(checked(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));C=json.loads(checked(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));fixed={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];raw=gzip.decompress(checked(root/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(raw,'little')%PRIME
result={}
for name,rows in (('parent',old),('sphere',new)):
 u=search(rows,vars,out);f=search(rows,vars,out,fixed=fixed);a=alias_and_square_sign(rows,vars,out)
 for run in (u,f):assert not run['counts']['targets_with_sample_zero'] and not run['counts']['sample_zero_nonconstant']
 result[name]={'uniform':u,'fixed':f,'alias_sign_uniform':a}
# Real double-negation alias control on a modified output wire.
control=old[:-1]+[['__neg_one__','-',0,old[-1][2]],['__neg_two__','-',0,'__neg_one__'],[old[-1][0],old[-1][1],'__neg_two__',old[-1][3]]];test=alias_and_square_sign(control,vars,out);assert test['aliases']
print(json.dumps({'results':result,'positive_control':test,'sphere_graph_delta':'Fam removed, Fa squared, final constant subtraction','scope':'bounded modular exact-target screen; alias/sign uniform only; no Lean or global lower bound'},sort_keys=True,indent=2))
