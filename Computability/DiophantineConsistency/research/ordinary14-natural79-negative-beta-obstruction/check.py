#!/usr/bin/env python3
"""Exact counterexample to positive w for arbitrary signed beta; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
t=pin('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36')
assert len(g['source'])==79 and len(g['witnesses'])==14
rows=[]
block=t.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
for line in block.splitlines():
 if not line.strip():continue
 m=re.fullmatch(r'\s*let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)\s*',line);assert m,line
 n,x,op,y=m.groups();v=lambda z:int(z) if z.isdecimal() else z
 rows.append([n,op,v(x),v(y)])
assert rows==g['source']
assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var (\d+)',t)==[(v,str(i)) for i,v in enumerate(g['witnesses'])]
assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.constant \(p (\d+)\)',t)==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])]
assert g['output']=='out'
assert [v.strip() for v in re.search(r'-- END LITERAL GRAPH\s*⟨([^⟩]+)⟩',t).group(1).split(',')][:6]==['F0','F1','Fa','Fs','guard','out']
ports=[-1,0,3,0];witness=[1,0,0,2,2,0,0,0,1,0,0,1,0,1]
assert len(ports)==4 and len(witness)==14 and all(v>=0 for v in witness) and witness[6]==0
values=dict(zip(g['witnesses'],witness));values.update(zip(g['fixed_numerals'],ports))
for n,op,x,y in rows:
 a=values[x] if isinstance(x,str) else x;b=values[y] if isinstance(y,str) else y
 values[n]=a+b if op=='+' else a-b if op=='-' else a*b
selected={k:values[k] for k in ('q','X','Y','U','a','H','Delta','c','R','Dstar','F0','F1','Fa','Fs','guard','out')}
assert selected=={'q':0,'X':0,'Y':0,'U':0,'a':0,'H':3,'Delta':3,'c':1,'R':1,'Dstar':0,'F0':1,'F1':1,'Fa':1,'Fs':1,'guard':1,'out':0}
print(json.dumps({'scope':'exact integer arithmetic on pinned JSON and row-identical Lean expression; no Lean elaboration or fixed-port theorem',
 'ports_by_name':dict(zip(g['fixed_numerals'],ports)),'natural_witness_by_name':dict(zip(g['witnesses'],witness)),
 'selected_graph_values':selected,'counterexample_to_unconditional_w_positivity':True,
 'beta_is_natural':False,'fixed_compact_port_case_checked':False},sort_keys=True,indent=2))
