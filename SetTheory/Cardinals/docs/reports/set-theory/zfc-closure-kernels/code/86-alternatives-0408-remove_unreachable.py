#!/usr/bin/env python3
"""Fold query's proved-unreachable prefix000 role into the root selector role."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,argparse
import build_library as B
p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
m=json.loads((a.input/'manifest.json').read_text());opts=dict(m['build_options']);opts['omit_unreachable_query']=True;d=B.build_retained(**opts)
classes=[g[:]for g in m['classes']];dead='query:127';old=next(g for g in classes if dead in g);assert old==[dead];classes.remove(old)
next(g for g in classes if 'query:121'in g).append(dead)
classes=[sorted(g)for g in classes];pi={q:i for i,g in enumerate(classes)for q in g};ports={q:len(classes)+i for i,q in enumerate(sorted(d['ports']))};pi.update(ports)
t={};cert=[]
for i,g in enumerate(classes):
 for b in (0,1):
  eligible=[q for q in g if b in d['domains'][q]];chosen=eligible[0]if eligible else g[0]
  w,move,target=d['rows'][chosen,b];t[i,b]=(w,move,pi[target])
  for q in eligible:
   w0,m0,t0=d['rows'][q,b];assert t[i,b]==(w0,m0,pi[t0]);cert.append([q,b,i,w0,m0,pi[t0]])
r={'table':t,'projection':pi,'classes':classes,'ports':ports,'entries':{k:pi[q]for k,q in d['entries'].items()},'structural':cert,'universal_classes':m['universal_classes'],'pairs':[]}
x=B.save(d,r,a.output);x['forced_symbol_savings']=None;x['packing_method']='Guarded congruence plus separately certified unreachable prefix000 role';x['source_manifest']=str(a.input/'manifest.json')
(a.output/'manifest.json').write_text(json.dumps(x,indent=2)+'\n');(a.output/'unreachable_certificate.json').write_text(json.dumps(d['reachability_certificate'],indent=2)+'\n')
print(json.dumps({k:x[k]for k in ('working_states','rows','sha256')},indent=2))
