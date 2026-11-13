from pathlib import Path
from hashlib import sha256
import ast,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('reviews/current2011-adaptive87-ipra-standalone-independent');A=Path('research/current2011-adaptive87-ipra-standalone-source-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],check=True,stdout=subprocess.PIPE,timeout=30).stdout==(A/'receipt.json').read_bytes()
out=subprocess.run([sys.executable,'-I','-S','-B','research/adaptive-direct-ordinate86/verify_degree87_parent.py'],check=True,stdout=subprocess.PIPE,timeout=30).stdout
assert out==Path('research/adaptive-direct-ordinate86/verify_degree87_parent.out').read_bytes()
s=(A/'Adaptive87IPRAStandalone.lean.src').read_text();parent=Path('Lean/DiophantineConsistency/IPRAAdaptiveNativeZFC.lean').read_text();trans=Path('Lean/DiophantineConsistency/IPRA87TranslatedRefutation.lean').read_text()
def block(x,head):return x.split(head,1)[1].split('\n\n',1)[0]
assert block(s,'def noZero87 :')==block(parent,'def noZero87 :')
for t in ['IPRAEquationComposition.equationComparison noZero87','IPRA87TranslatedRefutation.translated_refutation IPRABoundedRhoZFC.zfcEquiv','(IPRAStandardTheory.provable_iff _).2 native_equivalence87','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:assert t in s,t
assert 'import DiophantineConsistency.IPRA86TranslatedRefutation' not in s
assert '∼(Semiformula.lMap embedding refutation)ᴺ' in trans
comp=Path('Lean/DiophantineConsistency/IPRAEquationComposition.lean').read_text();rho=Path('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean').read_text();std=Path('Lean/DiophantineConsistency/IPRAStandardTheory.lean').read_text()
for t in ['(heq : nativeTheory ⊢ φ 🡘 ∼(Semiformula.lMap embedding refutation)ᴺ)','(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding','nativeTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding']:assert t in comp,t
assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in rho
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in std
literal=Path('Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean').read_text();body=literal.split('def expressionAt87 (p : Fin 4 → ℤ) : Expr (Fin 13) :=',1)[1].split('\ntheorem maintained_as_context',1)[0]
g=json.loads(Path('research/adaptive-first-root-factor87/candidate.json').read_text())
variables=re.findall(r'^  let (\w+) : Expr \(Fin 13\) := \.var (\d+)$',body,re.M);ports=re.findall(r'^  let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)$',body,re.M)
assert variables==[(v,str(i)) for i,v in enumerate(g['witnesses'])] and ports==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])]
rows=[]
for name,rhs in re.findall(r'^  let (\w+) := (.+)$',body,re.M):
 node=ast.parse(rhs,mode='eval').body;assert isinstance(node,ast.BinOp) and type(node.op) in [ast.Add,ast.Sub,ast.Mult]
 def val(x):return x.id if isinstance(x,ast.Name) else x.value if isinstance(x,ast.Constant) and type(x.value)==int else None
 a,b=val(node.left),val(node.right);assert a is not None and b is not None
 rows.append([name,{ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(node.op)],a,b])
assert rows==g['source'] and len(rows)==87
assert 'expressionAt87 CurrentWindowCarry2011.ports' in literal and 'positiveShift expression87' in literal
snap=Path('reviews/ipra-adaptive-fixed-snapshot-prefix/sources/DiophantineConsistency')
for name in ['AdaptiveFirstRootFactor87Literal','IPRA87TranslatedRefutation','IPRAAdaptiveNativeZFC']:
 assert (snap/(name+'.lean')).read_bytes()==Path('Lean/DiophantineConsistency',name+'.lean').read_bytes()
state=[json.loads(Path('reviews/ipra-adaptive-native-fixed-continuation-verification/'+x+'-state.json').read_text()) for x in ['author','independent']]
for name in ['DiophantineConsistency.IPRA87TranslatedRefutation','DiophantineConsistency.IPRAAdaptiveNativeZFC','DiophantineConsistency.IPRAAdaptiveNativeZFCChecks']:
 a,b=[[r for r in j['records'] if r.get('name')==name] for j in state];assert len(a)==len(b)==1 and a[0]['exit']==b[0]['exit']==0
 assert a[0]['object_sha256']==b[0]['object_sha256'] and a[0]['log_sha256']==b[0]['log_sha256']
 assert {k:v['sha256'] for k,v in a[0]['direct_imports'].items()}=={k:v['sha256'] for k,v in b[0]['direct_imports'].items()}
assert all(j['status']=='PASS' for j in state)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_and_degree_checks_reproduced':True,'exact_source_rows':len(rows),'no_zero_matches_historical_source':True,'native_standard_gg_directions_checked':True,'historical_paired_endpoint_rows_match':True,'lean_executed':False,'standalone_elaborated':False},sort_keys=True,indent=2))
