#!/usr/bin/env python3
"""Construct the unshift-s probe only; not a new consistency candidate."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'
p=json.loads(b);assert ['shift_s','+','n_s',1] in p['source']
def sub(x):return 'n_s' if x=='shift_s' else x
rows=[[n,o,sub(a),sub(c)] for n,o,a,c in p['source'] if n!='shift_s']
probe={'scope':'Boundary probe only; no consistency equivalence asserted.','parent_sha256':hashlib.sha256(b).hexdigest(),'domain':p['domain'],'witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'probe.json').write_text(json.dumps(probe,indent=2)+'\n')
