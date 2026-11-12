#!/usr/bin/env python3
"""Fold the shared zeta shift and the rank-offset subtraction exactly."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'
p=json.loads(b);rows=[]
for r in p['source']:
 if r[0] in {'shift_zeta','g52'}:continue
 if r[0]=='k':rows.extend([['kbase','+','shift_eta','n_zeta'],['k','+','kbase',1]])
 elif r[0]=='r0':rows.append(['r0','-','kbase','R'])
 else:rows.append(r)
c={'scope':'Exact all-port refactoring; inherited zero-map and iPRA limitations.','parent_sha256':hashlib.sha256(b).hexdigest(),'domain':p['domain'],'witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'candidate.json').write_text(json.dumps(c,indent=2)+'\n')
