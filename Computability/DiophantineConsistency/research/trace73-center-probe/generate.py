#!/usr/bin/env python3
"""Materialize the exact 75-to-73 center-substitution DAG, without equivalence claims."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,os,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent;d=h.parents[1];parent=d/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json';out=h/'candidate.json'
raw=parent.read_bytes();expected='8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9'
if sha256(raw).hexdigest()!=expected:raise ValueError('parent pin')
if os.path.lexists(out):raise FileExistsError(out)
g=json.loads(raw);rows=g['source'];assert len(rows)==75
removed=[r for r in rows if r[0] in {'LBt','center'}]
if removed!=[['LBt','*','V2','Bt'],['center','-','n','LBt']]:raise ValueError('unexpected rows')
source=[]
for name,op,a,b in rows:
 if name in ('LBt','center'):continue
 source.append([name,op,'n' if a=='center' else a,'n' if b=='center' else b])
counts=dict(Counter(x[1] for x in source))
if len(source)!=73 or counts!={'*':43,'+':17,'-':13}:raise ValueError('count')
result={'name':'trace73_center_positive_probe','domain':g['domain'],'witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],'coefficient_binding':g['coefficient_binding'],'source':source,'output':g['output'],'operations':73,'operation_breakdown':counts,'degree_upper_bound':352,'parent_sha256':expected,'substitution':'old n = new n + V2*Bt','status':'CONDITIONAL ALGEBRAIC PROBE: no all-model halt equivalence, no positivity proof, no iPRA endpoint'}
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'GENERATED','sha256':sha256(out.read_bytes()).hexdigest(),'rows':len(source),'counts':counts}))
