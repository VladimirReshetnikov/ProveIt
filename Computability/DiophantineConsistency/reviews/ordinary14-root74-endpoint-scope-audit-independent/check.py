#!/usr/bin/env python3
"""Independent source-scope controls, not Lean elaboration."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-endpoint-scope-audit'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'c71436f09f07486fcd6c94be59326bd8509e1f1623406f79a6a13207353f74c3',A/'check_source.py':'2973bb1740f1ec93e3541789c27b2a9a69cd1c08df7b8b33412dcdff5a0444db',A/'observation.json':'5ae622b43b01e2e9c75c0bd4fe3e26048569b55f81e07fe62388600c0c6f99d5'}
tail=b"\nIndependent source review: [root74 endpoint scope audit](../../reviews/ordinary14-root74-endpoint-scope-audit-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='8198f377ca6b86782dd04aae901629bd5d34a9eb15abc94a1f7e353bc1f73ce3'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert sha(p)==h,(str(p),sha(p),h)
def read(p):return (D/p).read_text()
def norm(s):return ' '.join(s.split())
e=read('research/ordinary14-root74-ipra-endpoint-draft/Root74Endpoint.lean')
for name,typ,rhs,body in [
 ('native_equivalence','nativeTheory','∼mappedNativeRefutation embedding','native_of_positive'),
 ('standard_equivalence','IPRAStandardTheory.standardTheory','∼mappedNativeRefutation embedding','standard_of_positive'),
 ('reference_equivalence','IPRAEqualityOnlyReference.referenceTheory','∼IPRAOrderErasure.erase (mappedNativeRefutation embedding)','reference_of_positive')]:
 m=re.search(r'theorem\s+'+name+r'\s*:\s*(.*?)\s*:=\s*(\w+)\s+_\s+Root74PositiveBridgeDraft\.positiveBridge',e,re.S);assert m and m.group(2)==body,name
 stmt=norm(m.group(1));assert stmt.startswith(typ+' ⊢ ') and stmt.endswith(rhs), (name,stmt)
 assert 'nativeNoZero (positiveShift Root74PositiveBridgeDraft.expression)' in stmt
 if name=='reference_equivalence':assert 'IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero' in stmt
b=read('research/ordinary14-root74-positive-bridge-draft/Root74PositiveBridge.lean')
assert 'open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts' in b
assert '(P74PositiveGuard.graph CompactSymbolicModelIff.p).output' in b
assert 'hpair.symm.trans (Root78PositiveBridgeDraft.positiveBridge V)' in b
rho=read('Lean/DiophantineConsistency/FoundationHAConsistencyNormalization.lean')
assert 'provabilityPred (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)' in rho
assert 'theorem source_eq_neg_rho : sourceSentence = ∼rho := rfl' in rho
assert 'native (Semiformula.lMap f rho)' in read('Lean/DiophantineConsistency/IPRAFoundationZFCMappedNegation.lean')
assert 'def rho : ℕ := 2^67' in read('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean')
assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in read('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean')
nozero=read('Lean/DiophantineConsistency/IPRAExpressionNative.lean')
assert '∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq' in nozero and 'e.splitNatural.1' in nozero and 'e.splitNatural.2' in nozero
candidate=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes());graph=read('research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean')
text=graph.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
lets=re.findall(r'^\s*let\s+(\w+)\s*:=\s*(\w+|\d+)\s*([+*\-])\s*(\w+|\d+)\s*$',text,re.M)
assert len(lets)==len(candidate['source'])==74
assert lets==[(str(n),str(x),op,str(y)) for n,op,x,y in candidate['source']]
assert candidate['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma','h']
for i,name in enumerate(candidate['witnesses']):assert re.search(r'let\s+'+name+r'\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var\s+'+str(i)+r'\b',graph)
inv=json.loads((D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json').read_bytes());rows=inv['drafts_topological']+inv['qualified_direct_sources'];paths={r['path'] for r in rows};assert len(rows)==len(paths)==190
tracked=set(subprocess.check_output(['git','ls-files','--',*sorted(paths)],cwd=D,text=True).splitlines());dirty=subprocess.check_output(['git','diff','--name-only','HEAD','--',*sorted(paths)],cwd=D,text=True).splitlines();assert tracked==paths and not dirty
for row in rows:assert sha(D/row['path'])==row['sha256'],row['path']
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'independent source interfaces, exact literal rows and tracked source boundary; no Lean or full provider audit','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'verified_literal_rows':len(lets),'verified_tracked_sources':len(paths),'author_receipt_replayed':True},sort_keys=True,indent=2))
