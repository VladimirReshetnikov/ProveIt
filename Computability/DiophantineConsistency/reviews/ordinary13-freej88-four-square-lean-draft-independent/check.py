#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-freej88-four-square-lean-draft'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'045da0d88af7b80ec52b6f56c828fe507917008290bebfad06e4254ad8ea0307','P88FourSquareGraph.lean':'614cb3ed5a91e919b5e44a5ae7f4fa7210a0a8b41bf5953d99d54c303b4f042e','P88FourSquareModel.lean':'1fb9d7a6d1b906c87877c3146787c5fea5558f2473aac029b7be702763df7192','P88FourSquareEndpoint.lean':'73260f5641e2d2d177e86d87e03af2e8dbcd8ef8b3829cc0cb55703dbaad07f9','make_graph.py':'3e64cace1ca7f8829e4693498f42a5f0b22d1c15c3c85a66a3e8e4d68fdb17af','preflight.py':'b03797cb95a516665f38956aab21743380150c5267cbe78ae84bfea7a28079e9','observation.json':'6f0f9f37a1086a495f50ed883664d6dd0dd16922ec65323d1e709a313389da2d'}.items():assert sha(p/n)==h
candidate=base/'research/ordinary13-four-square88-30/candidate.json';audit=base/'reviews/ordinary13-four-square88-30-independent/check.py';parent=base/'research/ordinary13-freej88-lean-draft/P88PairGraph.lean';parentmodel=base/'research/ordinary13-freej88-lean-draft/P88PairModel.lean'
for q,h in [(candidate,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(audit,'0883709a84091c0c6ff099bbf39bb9a60bf9a3f4cff7433f83a2718ade027167'),(parent,'a792a7731d88b61483f34bf6fea4ef46a983d7e95b19cf9f891f622691ac49f2'),(parentmodel,'21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
g=json.loads(candidate.read_text());lean=(p/'P88FourSquareGraph.lean').read_text();b=lean.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
def atom(x):
 if isinstance(x,ast.Name):return x.id
 assert isinstance(x,ast.Constant) and type(x.value)==int;return x.value
for line in b.splitlines():
 m=re.fullmatch(r'  let (\w+) := (.+)',line);assert m;n=ast.parse(m[2],mode='eval').body;assert isinstance(n,ast.BinOp);rows.append([m[1],{ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(n.op)],atom(n.left),atom(n.right)])
assert len(rows)==88 and rows==g['source']
variables=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.var (\d+)',lean);ports=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)',lean)
assert variables==[(n,str(i)) for i,n in enumerate(g['witnesses'])] and variables[0]==('J','0') and ports==[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])]
assert '  ⟨A0, A1, Fa, g72, out⟩' in lean
old=parent.read_text().split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0].splitlines();new=b.splitlines()
assert old[:old.index('  let Fs := 1 + g72')]==new[:new.index('  let g74 := T * c')]
assert '  let Fs := 1 + g72' not in new and '  let Fsm2 := g72 * g72' in new
assert '(P88Pair.graph p).strong = 1 + (graph p).gap' in lean and '[CommRing R]' in lean and '(graph p).output.evalRing w' in lean
model=(p/'P88FourSquareModel.lean').read_text();endpoint=(p/'P88FourSquareEndpoint.lean').read_text();prior=(base/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','InternalZero (P88FourSquare.graph p).output v ↔','InternalZero (P88Pair.graph p).output v','(P88PairModel.zero_iff p v).mp hz','FreeJ13.factor_units p v hp','rw [FreeJ13.unit_iff_one] at h0 h1 ha hs','rw [P88Pair.A0_eq]','rw [P88Pair.A1_eq]','rw [P88Pair.aux_eval_eq]','rw [P88Pair.strong_eq]','(P88PairModel.positiveBridge V).mp','(P88PairModel.positiveBridge V).mpr','(zero_iff _ v).mp hz','(zero_iff _ v).mpr hz','CompactSymbolicModelIff.p'):assert x in model
for name in ('native_equivalence','standard_equivalence','reference_equivalence'):
 def statement(s):return s.split('theorem '+name+' :',1)[1].split(':=',1)[0].strip()
 assert statement(endpoint).replace('P88FourSquareModel.expression','expression')==statement(prior)
for n in ('native_of_positive','standard_of_positive','reference_of_positive'):assert n+' _ P88FourSquareModel.positiveBridge' in endpoint
for s in (lean,model,endpoint):assert not re.search(r'\b(sorry|admit|axiom)\b',re.sub(r'#print axioms.*','',s))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'preflight.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr;x=json.loads(r.stdout);f=json.loads((p/'observation.json').read_text())
for a in (x,f):assert a['status']=='SOURCE_ONLY_NOT_LAUNCH_APPROVAL' and a['literal_rows']==88 and a['coordinates']==13 and a['arbitrary_integer_ports']==4 and a['candidate_parent_pin']=='PASS' and a['disk_above_stop_at_sample']==(a['tmp_free_bytes']>a['disk_stop_bytes'])
assert {k:v for k,v in x.items() if k not in ('tmp_free_bytes','disk_above_stop_at_sample')}=={k:v for k,v in f.items() if k not in ('tmp_free_bytes','disk_above_stop_at_sample')}
print(json.dumps({'status':'PASS_SCOPED_SOURCE_REVIEW','literal_rows':88,'first_coordinate':'free J','arbitrary_integer_ports':4,'frozen_tmp_free_bytes':f['tmp_free_bytes'],'fresh_tmp_free_bytes':x['tmp_free_bytes'],'fresh_above_floor':x['disk_above_stop_at_sample'],'scope':'Uncompiled source only; parent also uncompiled, no Lean theorem, signed-integer formalization, file binding or readiness.'},indent=2))
