#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-share91-lean-draft'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'P73Shared91.lean':'6fca39ca8af4743a9be256594cd87b2628d6b8c8e87107b08d604556e43bf364','P73Shared91Model.lean':'c2aa3ec2a50c714f59bd4c61589e5fd460af2d641ed67111cbaabf2d97ddcdd5','P73Shared91Endpoint.lean':'7314625ae4cb2a4fb99c607be47f252444c5304d2bfc2c73c75160df820c3746','README.md':'39cff82683e8dbe58400a601b742381366a786e558a8700660479542efab8cff','make_source.py':'6892107d3070b30718cd7de35f226f968fba194196d477e94b085da645c2b7db','preflight.py':'7f1feea6bf85bba45cd0f53efe881c43f6716fb7eb45f5f5b6d816de52d560be','preflight-observation.json':'3dc1474c9876f2e4fbb9edd1f7fd0c8b071ff13603bcab727241e0a43942cdfa'}.items():assert sha(p/n)==h
src=base/'Lean/DiophantineConsistency/Compact44/P73Graph.lean';endpoint=base/'Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean';candidate=base/'research/ordinary13-p73-triangular91-50/p73_rewrite91_30.json';review=base/'reviews/ordinary13-p73-triangular90-50-independent/check.py'
for f,h in [(src,'37537ef46555cde7a8a1017995988b6ca9ce6a121f07ebe70b0219951758dcac'),(endpoint,'b62f982919727f25e5a6e14cb6dfdbe80cb602b8b9b346ce3510d3e006920396'),(candidate,'474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180'),(review,'70e1159e2d433676d8782c2bf4c983a9a25936ad3067f51c7796e1058f884c19')]:assert sha(f)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
old=src.read_text(); draft=(p/'P73Shared91.lean').read_text();start='def graph (p : Fin 4 → ℤ) : Graph :=';end='\ntheorem output_eq';oldblock=old[old.index(start):old.index(end,old.index(start))]
oldblock=oldblock.replace(start,'def graph91 (p : Fin 4 → ℤ) : P73Graph.Graph :=')
a='  let g22 := k * qm\n  let W := 1 + g22\n  let M := q3 * qm\n';b='  let g35 := W * q3\n';assert oldblock.count(a)==oldblock.count(b)==1
expected=oldblock.replace(a,'  let M := q3 * qm\n').replace(b,'  let g35 := q3 + k * M\n')
assert expected in draft
c=json.loads(candidate.read_text()); block=draft.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
# Parse each Lean arithmetic let via Python's expression AST; assign a name to
# the sole nested multiplication before comparing every row to the JSON.
rows=[]
def term(e):
 if isinstance(e,ast.Name):return e.id
 if isinstance(e,ast.Constant):assert type(e.value)==int and e.value>=0;return e.value
 if isinstance(e,ast.BinOp):
  A=term(e.left);B=term(e.right);op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(e.op)]
  assert (A,op,B)==('k','*','M');rows.append(['kM',op,A,B]);return 'kM'
 raise AssertionError(ast.dump(e))
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (.+)',line);assert m
 node=ast.parse(m[2],mode='eval').body;assert isinstance(node,ast.BinOp)
 A=term(node.left);B=term(node.right);rows.append([m[1],{ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(node.op)],A,B])
assert len(rows)==91 and rows==c['source']
vars=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.var (\d+)',draft); ports=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)',draft)
assert vars==[(name,str(i)) for i,name in enumerate(c['witnesses'])] and ports==[(name,str(i)) for i,name in enumerate(c['fixed_numerals'])]
assert '  ⟨A0, A1, Aa, As, g91⟩' in draft
assert '(q + k * (q * m)).evalRing w = ((1 + k * m) * q).evalRing w' in draft
assert '[CommRing R]' in draft and '(p : Fin 4 → ℤ) (w : Fin 13 → R)' in draft
# Verify goal direction, composition and proposed adapters against the existing source.
model=(p/'P73Shared91Model.lean').read_text();e=(p/'P73Shared91Endpoint.lean').read_text();up=endpoint.read_text()
for t in ('InternalZero (P73Shared91.graph91 p).output v ↔','InternalZero (P73Graph.graph p).output v','(zero_iff _ v).1 hz','(zero_iff _ v).2 hz','Iff.trans ?_ (IPRAPositive73.positiveBridge V)','portsInt (paramKernel rho)'):assert t in model
for a in ('native_of_positive','standard_of_positive','reference_of_positive'):
 assert f'{a} _ positiveBridge' in e and f'{a} _ positiveBridge' in up
for n in ('native_equivalence','standard_equivalence','reference_equivalence'):
 def statement(s):return s.split('theorem '+n+' :',1)[1].split(':=',1)[0].strip()
 assert statement(e)==statement(up)
for s in (draft,model,e):assert not re.search(r'\b(sorry|admit|axiom)\b',re.sub(r'#print axioms.*','',s))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'preflight.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr
now=json.loads(r.stdout);frozen=json.loads((p/'preflight-observation.json').read_text())
for v in (now,frozen):
 assert v['source_pins']=='PASS' and v['literal_graph_rows_match']==91 and v['provider_authentication']=='NOT_ESTABLISHED' and v['runtime_disk_stop_bytes']==5100000000 and v['lean_launch_readiness'].startswith('BLOCKED:')
 assert v['disk_above_stop_at_sample']==(v['tmp_free_bytes']>v['runtime_disk_stop_bytes'])
print(json.dumps({'status':'PASS_SCOPED_SOURCE_REVIEW','literal_rows':len(rows),'proposed_ports':'arbitrary Fin 4 to integer','model_transfer':'both directions, conditional on provider','frozen_tmp_free_bytes':frozen['tmp_free_bytes'],'fresh_tmp_free_bytes':now['tmp_free_bytes'],'fresh_above_floor':now['disk_above_stop_at_sample'],'scope':'Read-only source review; no Lean compilation, kernel proof, authenticated provider closure, JSON/PDF binding or runner readiness.'},indent=2))
