#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-freej88-lean-draft'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'2ba4cc64e711c14a02192ab64f95d837dc7eff3cb71deca79c7c573c6298b4a0','P88PairGraph.lean':'a792a7731d88b61483f34bf6fea4ef46a983d7e95b19cf9f891f622691ac49f2','P88PairModel.lean':'21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a','P88PairEndpoint.lean':'41682e57745920cfbe57e6198db41312976b7722f329c2b989a1e98d3d41eebf','make_graph.py':'06545ce2a9d19a36b25d42f1b0a1d926fedb8dbdd500386436c173aa81eb966d','preflight.py':'3b80045b63f418e93738dc5126e4a696eea6e795da6211347662c7c1bdafee0c','preflight-observation.json':'d1d33f1f8fb1763c053ad9342891a6eb3f2901564a33fd90dff0b742caf216f2'}.items():assert sha(p/n)==h
candidate=base/'research/ordinary13-ordinary-pair88-46/freej88.json';review=base/'reviews/ordinary13-ordinary-pair88-46-independent/check.py';provider=base/'research/ordinary13-p73-provider-preflight/observation.json'
for q,h in [(candidate,'fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'),(review,'8d4629946284f383d149fe00b631ced0f3ec957f9ca9bff1880d8090ca42e74b'),(provider,'f37f6add7288d06a4e1ba60b97bc0ea5c00eeac13c5372bdceea4174c88bdae5')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
g=json.loads(candidate.read_text());lean=(p/'P88PairGraph.lean').read_text();b=lean.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
def atom(x):
 if isinstance(x,ast.Name):return x.id
 assert isinstance(x,ast.Constant) and type(x.value)==int;return x.value
for line in b.splitlines():
 m=re.fullmatch(r'  let (\w+) := (.+)',line);assert m;node=ast.parse(m[2],mode='eval').body;assert isinstance(node,ast.BinOp);rows.append([m[1],{ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(node.op)],atom(node.left),atom(node.right)])
assert len(rows)==88 and rows==g['source']
vars=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.var (\d+)',lean);ports=re.findall(r'  let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)',lean)
assert vars==[(n,str(i)) for i,n in enumerate(g['witnesses'])] and ports==[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])] and vars[0]==('J','0') and '  ⟨A0, A1, Fa, Fs, out⟩' in lean
parent=(base/'Lean/DiophantineConsistency/Compact44/FreeJ13.lean').read_text();oldblock=parent.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];oldlines=oldblock.splitlines();newlines=b.splitlines();assert oldlines[:oldlines.index('  let g80 := V * V')]==newlines[:newlines.index('  let g80 := g78 + V')]
assert '  let g81 := u * g80' in newlines and '  let g81 := y2 - g80' in oldlines
assert '[CommRing R]' in lean and '(u * ((v + u) + v)).evalRing w' in lean and '(((v + u) * (v + u)) - v * v).evalRing w' in lean
assert '(FreeJ13.graph p).A0' in lean and '(FreeJ13.graph p).strong' in lean and 'theorem output_eval' in lean
assert 'theorem factor_units' in parent and 'theorem unit_iff_one' in parent and '(graph p).strong * ((graph p).aux * ((1 + (graph p).A0) * (1 + (graph p).A1))) - 1' in parent
model=(p/'P88PairModel.lean').read_text();endpoint=(p/'P88PairEndpoint.lean').read_text();prior=(base/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean').read_text()
for snippet in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','InternalZero (P88Pair.graph p).output v ↔','InternalZero (FreeJ13.graph p).output v','FreeJ13.factor_units p v hz','rw [FreeJ13.unit_iff_one] at h0 h1 ha hs','have hpair :','rw [internalZero_iff, FreeJ13.output_eq]','CompactSymbolicModelIff.p','(zero_iff _ v).mp hz','(zero_iff _ v).mpr hz','FreeJ13Halt.positive_model_iff'):assert snippet in model
for name in ('native_equivalence','standard_equivalence','reference_equivalence'):
 def statement(s):return s.split('theorem '+name+' :',1)[1].split(':=',1)[0].strip()
 assert statement(endpoint).replace('P88PairModel.expression','expression')==statement(prior)
for n in ('native_of_positive','standard_of_positive','reference_of_positive'):assert n+' _ P88PairModel.positiveBridge' in endpoint
for s in (lean,model,endpoint):assert not re.search(r'\b(sorry|admit|axiom)\b',re.sub(r'#print axioms.*','',s))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'preflight.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr
fresh=json.loads(r.stdout);frozen=json.loads((p/'preflight-observation.json').read_text())
for x in (fresh,frozen):
 assert x['status']=='READ_ONLY_OBSERVATION_NOT_LAUNCH_APPROVAL' and x['source_pins']=='PASS' and x['literal_graph_rows_match']==88 and x['witnesses']==13 and x['integer_ports']==['beta','K0','MC','MF'] and x['launch_readiness'].startswith('BLOCKED:')
 assert x['disk_above_stop_at_sample']==(x['tmp_free_bytes']>x['disk_stop_bytes']) and len(x['p72_frontier_point_observations'])==5
 for y in x['p72_frontier_point_observations'].values():assert y['exists'] and y['matches_prior_point_hash']
assert {k:v for k,v in fresh.items() if k not in ('tmp_free_bytes','disk_above_stop_at_sample')}=={k:v for k,v in frozen.items() if k not in ('tmp_free_bytes','disk_above_stop_at_sample')}
print(json.dumps({'status':'PASS_SCOPED_SOURCE_REVIEW','literal_rows':88,'first_coordinate':'free J','arbitrary_integer_ports':4,'p72_point_hashes':5,'frozen_tmp_free_bytes':frozen['tmp_free_bytes'],'fresh_tmp_free_bytes':fresh['tmp_free_bytes'],'fresh_above_floor':fresh['disk_above_stop_at_sample'],'scope':'Uncompiled source and point-provider observation only; no signed-integer Lean result, P73 coordinate identification, JSON/PDF binding or build readiness.'},indent=2))
