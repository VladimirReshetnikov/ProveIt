#!/usr/bin/env python3
"""Audit binding, coverage, arithmetic and row references of a runtime report.

This is a structural independent audit of the full symbolic result, not a
second implementation of the symbolic proof rules themselves.
"""
import argparse,hashlib,json,re
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
for name in ['table','sites','report','cases','mapping','output']:ap.add_argument(name,type=Path)
a=ap.parse_args();raw=a.table.read_bytes();srcraw=a.sites.read_bytes();sites=json.loads(srcraw);r=json.loads(a.report.read_text());cases=json.loads(a.cases.read_text());T={}
for line in raw.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=int(w),1 if d=='R'else-1,int(z)
mapping={int(q):v for q,v in json.loads(a.mapping.read_text()).items()}
for q in {q for q,b in T}|{z for w,d,z in T.values()}:
 if q not in mapping:mapping[q]=q+1000
assert len(set(mapping.values()))==len(mapping)
L={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()}
assert r['status']=='ALL_PRIMITIVE_INTERFACES_PROVED' and r['working_states']==219
assert r['table_sha256']==hashlib.sha256(raw).hexdigest() and r['source_sha256']==hashlib.sha256(srcraw).hexdigest()
guards=[(i,positive)for i,(_,op,arg)in enumerate(sites)for positive in((False,True)if op=='CD'else(False,))]
assert len(guards)==len(cases)==r['cases']==6167

def strip(pc,b,n):
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==b:
   n-=1
   if n==0:return pc[:i]
 return ''
def overflow(pc):return int(not pc or set(pc)=={'1'})
for want,c in zip(guards,cases):
 assert (c['index'],c['positive'])==want
 assert set(c['kinds'])<={'literal','unary','list'} and sum(c['kinds'].values())==c['symbolic_steps']
 assert len(c['duration'])==len(c['motion'])==13 and all(type(n)is int and n>=0 for n in c['duration'])and c['duration'][0]>0
 pc,op,arg=sites[c['index']]
 if op!='CH':
  shift=overflow(pc)if op=='CI'or(op=='CD'and c['positive'])else overflow(strip(pc,'0',arg if op=='CB'else 1))if op in('CB','CD')else 0
  assert c['motion']==[-shift]+[0]*12
assert sum(c['symbolic_steps']for c in cases)==r['symbolic_steps']==1515040
assert min(c['duration'][0]for c in cases)==r['minimum_actual_steps']==13
assert len(r['blocks'])==4
for lemma in r['blocks']:
 assert lemma['arbitrary_contexts']is True and lemma['steps']=='v+2'
 for e in lemma['trace']:
  assert e[0]in('literal','unary');q,b,w,d,z=e[1];assert L[q,b]==(w,d,z)
used={tuple(k)for k in r['used_rows']};assert used<=set(L)
for q,b in[(103,1),(108,1),(113,0),(198,0),(301,0),(301,1),(302,0),(302,1)]:assert(mapping[q],b)in used
trie={}
for pc,op,arg in sites:
 n=trie
 for b in pc:n=n.setdefault(b,{})
 assert not n;n['leaf']=(op,arg)
nodes=set()
def visit(n):
 t=('L',*n['leaf'])if'leaf'in n else('B',visit(n['0']),visit(n['1']))
 nodes.add(t);return t
visit(trie)
assert len(nodes)==206 and max(map(lambda s:len(s[0]),sites))==38 and max(len(z)for pc,op,arg in sites for z in pc.split('1'))==6
out={'status':'RUNTIME_REPORT_STRUCTURAL_AUDIT_PASS','table_sha256':r['table_sha256'],'sites_sha256':r['source_sha256'],'cases':len(cases),'distinct_guard_cases':len(set(guards)),'symbolic_steps':r['symbolic_steps'],'minimum_duration_constant':13,'maximum_symbolic_steps_per_case':max(c['symbolic_steps']for c in cases),'block_schema_traces':4,'source_dag_nodes':len(nodes),'checked_changed_rows':8,'scope':__doc__.strip()}
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
