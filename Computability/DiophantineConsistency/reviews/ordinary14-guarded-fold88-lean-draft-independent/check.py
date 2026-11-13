#!/usr/bin/env python3
"""Quotient-guard graph/source audit only; never invoke Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-guarded-fold88-lean-draft';Q=D/'reviews/ordinary14-guarded-fold89-lean-draft-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','834e48bdfc466d7713882aa8455f256faf8f681556e4940c8263f2de613f281c'),(P/'make_graph.py','6ffc30c6e5fdbc85a25a2f9d083cfc36cea013f6d036db2d271016fe801f998c'),(P/'P88QuotientGuardedGraph.lean','85d347c35b4ea21fe20651460c0df6f20adf0cc444f99b4e3c9a8a9d81d0097e'),(P/'observation.json','98e0354d88962d50068cf5c9eaabec69966544ebe6e278b0e7aa91bc36338da2'),(Q/'check.py','db9ad84848ef084464c5a3bcf58e2f2aeade9ce24506523791b016337d3c4539'),(Q/'result.json','90c9ae92474cd6a1fcd72efe3fa8c648b9064a7d60e215befe4680fa034b131b')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent source review is recorded in\n`../../reviews/ordinary14-guarded-fold88-lean-draft-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='8b54e436c22414ca9833ddc1775ddc2617b63d3bf34b15e9b2d37a1997f14b9e'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and r.stdout==(P/'observation.json').read_bytes()
r=subprocess.run([sys.executable,'-I','-S','-B',str(Q/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(Q/'result.json').read_bytes()
gp=D/'research/ordinary14-guarded-fold88-26/candidate.json';assert sha(gp)=='a3c5f7d9ed6f2c55a49818c5927f08b6293216bbecce24731a99890c83cc6ada';g=json.loads(gp.read_text());s=(P/'P88QuotientGuardedGraph.lean').read_text();block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert rows==g['source'] and len(rows)==88
for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert '⟨A0, A1, Fa, g72, Bt, qm, guarded_out⟩' in s and '(graph p).Bt - (graph p).b * .var 13' in s and 'by rfl' in s
rd={row[0]:row for row in rows}
for n,row in {'g31':['g31','-','g30','r'],'Z':['Z','+','g32','g33'],'bt_quotient':['bt_quotient','*','qm','t'],'guard':['guard','-','Bt','bt_quotient'],'guard2':['guard2','*','guard','guard'],'guarded_out':['guarded_out','+','out','guard2']}.items():assert rd[n]==row
print(json.dumps({'status':'PASS_SOURCE_ONLY','literal_rows':len(rows),'prior_89_source_review_reproduced':True,'generator_observation_reproduced':True,'scope':'uncompiled quotient-guard source; sigma_prime positivity, graph-specific model bridge, providers and endpoints remain open; no Lean'},indent=2))
