#!/usr/bin/env python3
"""Independent audit of fresh case results, with no certificate code imports."""
from pathlib import Path
import json,hashlib,argparse
from independent_small_audit import read_table,sha,dump

def blockproof(t,records):
 # Each token is bit^(constant + coefficient*n), n arbitrary natural.
 # Derive row transition on each constant cell and arbitrary unary self-loop.
 # All moves are monotone, hence exterior cells are untouched.
 schemas=[(73,1,[(0,1,0),(1,1,0),(1,0,1)],[(0,1,0),(1,1,1)]),
 (95,1,[(0,1,0),(1,1,0),(1,0,1)],[(1,1,0),(0,1,0),(1,0,1)]),
 (48,-1,[(1,1,0),(1,0,1),(0,1,0)],[(1,1,1),(0,1,0)]),
 (112,-1,[(1,0,1),(0,1,0),(1,1,0)],[(1,1,1),(0,1,0)])]
 def compact(tokens):
  out=[]
  for b,c,v in tokens:
   if out and b==out[-1][0]:out[-1]=(b,out[-1][1]+c,out[-1][2]+v)
   else:out.append((b,c,v))
  return out
 for rec,(entry,direction,word,target)in zip(records,schemas):
  q=entry;actual=[];proof=[]
  for b,c,v in word:
   w,d,z=t[q,b];assert d==direction
   if v:assert c==0 and v==1 and q==z
   else:assert c==1
   proof.append(['unary',[q,b,w,d,z],[0,0,1]+[0]*10]if v else['literal',[q,b,w,d,z]])
   actual.append((w,c,v));q=z
  assert q==entry and compact(actual)==target
  assert rec['entry']==entry and rec['direction']==direction and rec['steps']=='v+2'and rec['arbitrary_contexts']is True and rec['trace']==proof
 assert len(records)==4
 return 'Four arbitrary-n unary/list block identities; duration n+2; monotone traversal leaves arbitrary exterior untouched.'

def audit(release,receipts):
 results={}
 for n,d in receipts.items():
  folder=release/'machine'/n;t=read_table(folder/'k219.native.tm');sites=json.loads((folder/'sites.json').read_text());r=json.loads((d/'runtime.json').read_text());cs=json.loads((d/'cases.json').read_text());integrity=json.loads((d/'integrity.json').read_text())
  assert r['status']=='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED'and r['failures']==[]and r.get('generic_cases_excluded',0)==0
  assert r['table_sha256']==sha(folder/'k219.native.tm')and r['source_sha256']==sha(folder/'sites.json')
  for file,h in integrity['hashes'].items():assert sha(d/file)==h,(n,file)
  expected=[(i,b)for i,(_,o,a)in enumerate(sites)for b in((False,True)if o=='CD'else(False,))]
  assert[(c['index'],c['positive'])for c in cs]==expected
  assert len(cs)==r['cases']==r['expected_cases']==(6167 if n=='retagged' else 6175)
  for c in cs:
   assert type(c['index'])is int and type(c['positive'])is bool
   dur=c['duration'];assert len(dur)==13 and all(type(x)is int and x>=0 for x in dur)and dur[0]>0
   assert len(c['motion'])==13 and all(type(x)is int for x in c['motion'])
   assert 0<c['symbolic_steps']==sum(c['kinds'].values()) and set(c['kinds'])<={'literal','unary','list'}
  assert r['symbolic_steps']==sum(c['symbolic_steps']for c in cs)
  assert r['directly_used_rows']==[list(k)for k in sorted(t)]
  mp={int(k):v for k,v in r['mapping'].items()};assert len(set(mp.values()))==len(mp)and set(tq for tq,b in t)|{254}<=set(mp)
  assert(mp[0],mp[84],mp[254],mp[102],mp[120])==(95,96,254,1301,1302)
  remap={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
  bp=blockproof(remap,r['block_schemas'])
  results[n]=dict(status='STORED_FRESH_RUNTIME_EVIDENCE_INDEPENDENTLY_AUDITED',table_sha256=r['table_sha256'],source_sha256=r['source_sha256'],cases=len(cs),cases_sha256=sha(d/'cases.json'),runtime_sha256=sha(d/'runtime.json'),symbolic_steps=r['symbolic_steps'],minimum_duration_constant=min(c['duration'][0]for c in cs),row_coverage=438,generic_cases_excluded=0,independent_blocks=bp,proof_boundary='Audits the complete fresh run evidence; this audit does not regenerate all symbolic derivations.')
 return dict(status='INDEPENDENT_RUNTIME_RECEIPTS_AND_FOUR_BLOCKS_PASS',variants=results)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--release',type=Path,required=True);p.add_argument('--zero',type=Path,required=True);p.add_argument('--retagged',type=Path,required=True);p.add_argument('--composed',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();r=audit(a.release,dict(zero_terminal=a.zero,retagged=a.retagged,composed=a.composed));dump(a.out,r);print(json.dumps(r,indent=2))
