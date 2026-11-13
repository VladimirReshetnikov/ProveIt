#!/usr/bin/env python3
"""Independent bounded constructor/gate check and forward-source audit; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-norm38-forward-bridge-draft';C=D/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'Norm38Forward.lean','70dad9e40dd83aaca364972a1b84ba62f40594aeb5ad3b62b992e66078821837'),(P/'check.py','2bcb4104070cee7f170b0f1e79a12a146c8a1eaa1ab1050d03caa0b6414e3a97'),(P/'result.json','be5213d2eee60ffeadbeaf4bb5c9d87ba19d226562a9aaed1279e3ecc1e33772'),(C/'ForwardWitness38.lean','559de61d5eeeb17ef2f6c449f4d594e242ab1c784ce4b34ba58753898209ad14'),(C/'NormAssignment38.lean','c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a')]:need(sha(p)==h,'pin '+str(p))
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True,timeout=120);need(q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes(),'author source check')
s=(P/'Norm38Forward.lean').read_text();need('∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in s and '(hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))' in s and '(hs : InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1))' in s,'source hypotheses');need('SharingForward38.witnessCoordinates ports u' in s and 'Fin.cons (1 : V)' in s,'output witness');need('rw [hscale,hStrong,mul_one]' in s,'strong scale no division');need('sub_eq_zero.mpr hns' in s and 'static_implies_seed_zero' in s,'scaled norm direction')
f=(C/'ForwardWitness38.lean').read_text();a=(C/'NormAssignment38.lean').read_text();ws=re.findall(r'^  let w(\d+) : S := (.+)$',f,re.M);nodes=re.findall(r'^  let a(\d+) : SignedPair S := (.+)$',a,re.M);gates=[(int(i),int(j),int(k),op) for i,j,k,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',a)];need([int(i) for i,_ in ws]==list(range(15,39)) and [int(i) for i,_ in nodes]==list(range(81)) and len(gates)==60,'enumeration')
def pair(op,x,y):
 ap,an=x;bp,bn=y
 if op=='add':return ap+bp,an+bn
 if op=='sub':return ap+bn,an+bp
 need(op=='mul','op');return ap*bp+an*bn,ap*bn+an*bp
def val(exp,ports,u,w,loc):
 exp=re.sub(r'\((\d+) : S\)',r'\1',exp);exp=re.sub(r'ports (\d+)',r'ports[\1]',exp);exp=re.sub(r'u (\d+)',r'u[\1]',exp);exp=re.sub(r'w (\d+)',r'w[\1]',exp)
 need(re.fullmatch(r'[\w\[\]() +*\-]+',exp) is not None,'unexpected expression');return eval(exp,{'__builtins__':{}},{'ports':ports,'u':u,'w':w,**loc})
for k in range(8):
 ports=[(k*i+i+2)%7 for i in range(4)];u=[(k+3*i)%5 for i in range(14)];loc={}
 for i,exp in ws:loc['w'+i]=val(exp,ports,u,[],loc)
 w=u+[loc['w'+str(i)] for i in range(15,39)];need(w[:14]==u and len(w)==38,'prefix');vals=[]
 for i,rhs in nodes:
  m=re.fullmatch(r'⟨(.+), (.+)⟩',rhs)
  if m:v=(val(m[1],ports,u,w,{}),val(m[2],ports,u,w,{}))
  else:
   m=re.fullmatch(r'pairCompute GateOp\.(add|sub|mul) a(\d+) a(\d+)',rhs);need(m is not None,'node '+i);v=pair(m[1],vals[int(m[2])],vals[int(m[3])])
  vals.append(v)
 for target,left,right,op in gates:need(vals[target]==pair(op,vals[left],vals[right]),'gate sample '+str((k,target)))
print(json.dumps({'status':'PASS_SCOPED_FORWARD_SOURCE_REVIEW','integer_samples':8,'gates_per_sample':len(gates),'slot_bindings':29,'scope':'Source and finite constructor checks only; no Lean model proof, fixed-port casts, current equation equivalence or iPRA endpoint.'},sort_keys=True,indent=2))
