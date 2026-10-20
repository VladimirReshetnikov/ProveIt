#!/usr/bin/env python3
"""Focused own-engine unbounded runtime checks for two raw220 source alternatives."""
import collections,hashlib,json,time
from pathlib import Path
import symbolic_contexts as own
D=Path(__file__).resolve().parent;ROOT=D.parent
prefixes=['111010010011101111000','11101001001110111110','1110100101100','111110']
allreports=[]
for name in ['09','13']:
 path=ROOT/f'research218_encoding/direct_equality_{name}/candidate.native.tm';sourcepath=ROOT/f'research218_source/direct_equality_{name}_sites.json'
 T=own.readtm(path);S=json.loads(sourcepath.read_text());schemas,_=own.prove_schemata(T)
 selected={i for i,(p,o,a) in enumerate(S) if any(p.startswith(q) for q in prefixes)}
 # Add first and longest-address representative of each arithmetic primitive
 # outside the changed macros, to probe unchanged-source arithmetic helpers.
 others=collections.defaultdict(list)
 for i,(p,o,a) in enumerate(S):
  if i not in selected and o in ['CI','CD']:others[o,a].append(i)
 for ids in others.values():selected.add(ids[0]);selected.add(max(ids,key=lambda i:len(S[i][0])))
 results=[];start=time.monotonic();rules=0
 for i in sorted(selected):
  for pos in [False,True] if S[i][1]=='CD' else [False]:
   try:
    n,_=own.case(T,schemas,S[i],pos,{});rules+=n
    results.append({'index':i,'site':S[i],'positive':pos,'status':'PROVED','symbolic_rules':n})
   except (AssertionError,KeyError,ValueError) as error:
    results.append({'index':i,'site':S[i],'positive':pos,'status':'NOT_PROVED','reason':str(error)[:2500]})
 report={'candidate':'direct'+name,'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(sourcepath.read_bytes()).hexdigest(),'selected_sites':len(selected),'cases':len(results),'passed':sum(r['status']=='PROVED' for r in results),'not_proved':sum(r['status']=='NOT_PROVED' for r in results),'rules_in_passed':rules,'seconds':time.monotonic()-start,'results':results,'scope':'Focused unbounded symbolic whole-frame cases only. Every changedmacro leaf/guard plus first/longest arithmetic representatives outside macros; not fullprimitive coverage or blankstartup. A NOT_PROVED case is not by itself a semantic counterexample.'}
 (D/f'DIRECT{name}_RUNTIME_PILOT.json').write_text(json.dumps(report,indent=2)+'\n');allreports.append(report)
 print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2),flush=True)
 for r in results:
  if r['status']=='NOT_PROVED':print('FAIL',r,flush=True)
