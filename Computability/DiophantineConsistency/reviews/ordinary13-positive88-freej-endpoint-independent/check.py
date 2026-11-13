from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive88-freej-endpoint-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-positive88-freej-endpoint-source-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
paths=['research/ordinary13-four-square88-30/candidate.json','research/ordinary13-ordinary-pair88-46/freej88.json','con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive13_87_degree51.json']
gs=[json.loads(Path(p).read_text()) for p in paths]
assert [len(g['source']) for g in gs]==[88,88,87]
assert all(g['witnesses']==gs[0]['witnesses'] and g['fixed_numerals']==gs[0]['fixed_numerals'] for g in gs)
def evalg(g,x,p):
 v=dict(zip(g['witnesses'],x));v.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  a=v[l] if isinstance(l,str) else l;b=v[r] if isinstance(r,str) else r
  v[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 return v
for t in range(240):
 x=[((t*(2*j+3)+j*j+5)%11)-5 for j in range(13)]
 p=[((t*(j+2)+j)%7)-3 for j in range(4)]
 a,b,c=(evalg(g,x,p) for g in gs)
 for f in ('A0','A1','Fa','g72','V','Q'):assert a[f]==b[f]==c[f],(t,f)
 A,B,F,S=a['A0'],a['A1'],a['Fa'],a['g72']+1
 assert a['out']==A*A+B*B+(F-1)**2+(S-1)**2
 assert b['out']==A*A+B*B+(F*S-1)**2
 assert c['P13']==S*F*(1+A)*(1+B)-1
# Abstract-factor control and implication table, not actual graph zero search.
assert (1-(-1))**2+(1-(-1))**2==8
controls=0
for A in range(-3,4):
 for B in range(-3,4):
  for F in range(-3,4):
   for S in range(-3,4):
    four=A*A+B*B+(F-1)**2+(S-1)**2
    paired=A*A+B*B+(F*S-1)**2
    product=S*F*(1+A)*(1+B)-1
    assert four!=0 or paired==0
    assert paired!=0 or product==0
    if (A,B,F,S)==(0,0,1,1):assert paired==0 and four==0 and product==0
    controls+=1
model=Path('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean').read_text()
pair=Path('research/ordinary13-freej88-lean-draft/P88PairModel.lean').read_text()
endpoint=Path('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareEndpoint.lean').read_text()
parent=Path('Lean/DiophantineConsistency/Compact44/FreeJ13.lean').read_text()
halt=Path('Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean').read_text()
for s,terms in [(model,['(P88PairModel.zero_iff p v).mp hz','FreeJ13.factor_units p v hp','(zero_iff _ v).mp hz','(zero_iff _ v).mpr hz']),(pair,['FreeJ13.factor_units p v hz','(FreeJ13Halt.positive_model_iff (V := V)).mp','(FreeJ13Halt.positive_model_iff (V := V)).mpr']),(endpoint,['nativeTheory ⊢','positiveShift P88FourSquareModel.expression','∼mappedNativeRefutation embedding','reference_of_positive _ P88FourSquareModel.positiveBridge']),(parent,['theorem factor_units (p : Fin 4 → ℤ) (v : Fin 13 → V)','theorem unit_iff_one']),(halt,['(∀ j, 0 < v j)','graph CompactSymbolicModelIff.p','ArithmeticMachineRun215.run T'])]:
 for term in terms:assert term in s,term
print(json.dumps({'author_receipt_exact':True,'pinned_files':len(json.loads((D/'pins.json').read_text())),'full_graph_signed_controls':240,'abstract_factor_controls':controls,'endpoint_replay':False,'lean_executed':False},sort_keys=True,indent=2))
