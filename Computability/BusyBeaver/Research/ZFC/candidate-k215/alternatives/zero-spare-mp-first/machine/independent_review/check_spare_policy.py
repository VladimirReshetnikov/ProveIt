#!/usr/bin/env python3
"""Positive and negative spare-policy controls using the unchanged runtime engine.
This one-case check does not replace the complete universal census.
"""
from pathlib import Path
import sys,json,os,argparse
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('Spare-policy checking requires enabled assertions')
R=Path(__file__).resolve().parent.parent;P=R/'parent/reference/transfer-parent';sys.path.insert(0,str(P/'checks'))
import independent_runtime as I,symbolic_runtime as S
ss=json.loads((R/'sites.json').read_text());i=next(i for i,s in enumerate(ss)if s[1]=='CI');site=ss[i]
m={int(k):int(v)for k,v in json.loads((P/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()}
T=I.table(R/'candidate.native.tm')
for q in sorted({q for q,b in T}|{254}):
 if q not in m:m[q]=max(m.values())+1
out={'source_ordinal':i,'source_site':site,'tests':[]}
for which,path,correct in [('new_zero',R/'candidate.native.tm',0),('parent_unit',R/'parent/machine/t215.native.tm',1)]:
 U={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in I.table(path).items()};lemmas,blocks=S.prove_blocks(U)
 for append in(0,1):
  try:
   c=S.case(U,lemmas,site,False,append=append)
  except AssertionError as e:
   assert append!=correct,(which,append,e)
   out['tests'].append(dict(table=which,append=append,expected='REJECT',result='REJECT',message=str(e)[:1000]))
  else:
   assert append==correct,(which,append,c)
   out['tests'].append(dict(table=which,append=append,expected='PASS',result='PASS'))
out['status']='SPARE_POLICY_POSITIVE_AND_NEGATIVE_CONTROLS_PASS'
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);a=ap.parse_args()
if a.out:a.out.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
