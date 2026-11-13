#!/usr/bin/env python3
"""Externally check generated reference rows, topology and source fields."""
import contextlib,hashlib,io,json,re,runpy,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];graph=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(graph)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());d=json.loads((P/'reference-rows.json').read_text());src=(P/'Norm38Reference.lean').read_text();assert 'UNCOMPILED DRAFT' in src and 'sorry' not in src and 'admit' not in src
assert d['source_graph_sha256']==sha(graph) and len(d['rows'])==60
indices={n:i for i,n in enumerate(g['witnesses'])};indices.update({n:i+14 for i,n in enumerate(g['fixed_numerals'])});indices.update({1:18,3:19,4:20});lines=re.findall(r'^  let a(\d+) : R := (.+)$',src,re.M);assert len(lines)==81 and [int(i) for i,_ in lines]==list(range(81))
for i in range(14):assert lines[i][1]==f'x {i}'
for i in range(4):assert lines[i+14][1]==f'p {i}'
for i,n in enumerate((1,3,4),18):assert lines[i][1]==str(n)
done=set(range(21))
for k,(row,entry) in enumerate(zip(g['source'][:60],d['rows'])):
 n,op,a,b=row;i=k+21;left,right=indices[a],indices[b]
 assert entry=={'index':i,'name':n,'op':op,'left':left,'right':right}
 assert left in done and right in done and i not in done
 assert lines[i][1]==f'a{left} {op} a{right}'
 indices[n]=i;done.add(i)
assert done==set(range(81));assert '  !['+', '.join('a'+str(i) for i in range(81))+']' in src
with contextlib.redirect_stdout(io.StringIO()):prev=runpy.run_path(str(D/'reviews/nine-sharing-quartic65-59-independent/source_check.py'))
for gate,field in [('N0','P'),('N1','Q'),('Na','U'),('Nt','W'),('scaled_Ns','Z'),('Delta','delta')]:assert prev['v'][gate]==prev['env'][field]
assert [indices[n] for n in ('N0','N1','Na','Nt','scaled_Ns','Delta')]==[61,44,78,66,80,36]
for frag in ['reference p x 61 = d.P','reference p x 44 = d.Q','reference p x 78 = d.U','reference p x 66 = d.W','reference p x 80 = d.Z','reference p x 36 = d.delta','Norm38SlotExtraction.seed_zero_static','FreshModel106.evalRing_expressionAt65']:assert frag in src
print(json.dumps({'status':'PASS_EXTERNAL_REFERENCE_BINDING_ONLY','source_sha256':sha(P/'Norm38Reference.lean'),'rows_sha256':sha(P/'reference-rows.json'),'nodes':81,'source_rows':60,'terminal_matches':{'N0':'P','N1':'Q','Na':'U','Nt':'W','scaled_Ns':'Z','Delta':'delta'},'scope':'Generated text, graph topology and previous external source DAG comparison; no Lean compile or all-model bridge.'},indent=2,sort_keys=True))
