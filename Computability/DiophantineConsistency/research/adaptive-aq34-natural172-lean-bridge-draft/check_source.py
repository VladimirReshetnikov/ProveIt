#!/usr/bin/env python3
"""Read-only exact DAG cancellation and inert source checks; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','1884e38b36c46ee5671c65246f6d8f459c02766a1b59559808b5cc977b01ea70')
obs=json.loads(pin(P/'result.json','64fa83dc5e938dc73df4452d34dfc4656ec774a08522c40c06503f447bad686e'))
old=json.loads(pin(D/'research/adaptive-square-sums34/candidate.json','9c7fdcf0289b0407af4bbb9deaef4d52fd37435c162a8d15199d1ec9902e1f77'))
new=json.loads(pin(D/'research/adaptive-aq34-natural172-signed-cancel/candidate.json','2bc8d1be1d3e4ca72dd84255816bda819bd75423447c6799c3aa52b8583d8f23'))
oldsrc=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ34Literal.lean','30e3a0e4bc8199bcb62d27bcc0cc6a73697027f9c0066d24cbaad340eb2df38b')
context=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ34Context.lean','2f581a4dcd732d0f4b5f1c2f39a183dba00d5f7cca37c725009dd505f98291cd')
endpoint=pin(D/'Lean/DiophantineConsistency/IPRAAQ34Native.lean','857f4eb24f59efabfb49b9e6ba038bc43d1ffd81af70b21827f4b68153f5a31d')
src={n:pin(P/n,h) for n,h in obs['source_hashes'].items()};lit=src['AQ34Natural172Literal.lean.src'];res=src['AQ34Natural172Residuals.lean.src'];bridge=src['AQ34Natural172Bridge.lean.src']
start=oldsrc.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 34) :=\n');end=oldsrc.index('\ntheorem new_literal ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 34) :=']+[f'  let {n} : Expr (Fin 34) := .var {i}' for i,n in enumerate(old['witnesses'])]+[f'  let {n} : Expr (Fin 34) := .constant (p {i})' for i,n in enumerate(old['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in old['source']]+['  '+old['output']]
assert oldsrc[start:end].splitlines()==expected and len(old['source'])==144
for i,n in enumerate(new['witnesses']):assert f'let {n} : Expr (Fin 34) := .var {i}' in lit
for i,n in enumerate(new['fixed_numerals']):assert f'let {n} : Expr (Fin 34) := .constant (p {i})' in lit
for n,o,a,b in new['source']:assert f'  let {n} := {a} {o} {b}\n' in lit
assert len(new['source'])==172 and len(new['witnesses'])==34
pairs={'namedBt':('wPositive','wNegative'),'Dstar':('dPositive','dNegative'),'V':('vPositive','vNegative')}
for n,(a,b) in pairs.items():
 assert [n,'-',a,b] in old['source'] and [r[0] for r in old['source'] if a in r[2:]]==[n] and [r[0] for r in old['source'] if b in r[2:]]==[n]
# Independent symbolic DAG interning: evaluate the positive shift of each
# parent row, cancel exactly the three indicated (x+1)-(y+1) patterns, then
# compare every resulting row to the actual 172-row candidate DAG.
pool={};desc=[]
def intern(x):
 if x not in pool:pool[x]=len(desc);desc.append(x)
 return pool[x]
one=intern(('int',1));shared={n:intern(('input','n_'+n)) for n in old['witnesses']};ports={n:intern(('port',n)) for n in old['fixed_numerals']}
parent={n:intern(('+',shared[n],one)) for n in old['witnesses']};parent.update(ports)
child={n:shared[n[2:]] for n in new['witnesses']};child.update(ports)
def value(env,x):return intern(('int',x)) if type(x)==int else env[x]
for n,o,a,b in new['source']:child[n]=intern((o,value(child,a),value(child,b)))
for n,o,a,b in old['source']:
 x,y=value(parent,a),value(parent,b)
 if n in pairs:
  A,B=desc[x],desc[y];assert o=='-' and A[0]=='+' and B[0]=='+' and A[2]==B[2]==one
  x,y=A[1],B[1]
 parent[n]=intern((o,x,y));assert parent[n]==child[n],n
assert parent[old['output']]==child[new['output']]
a=context.index('def residuals (p : Fin 4 → ℤ) : Fin 22');b=context.index('\ndef sum (p : Fin 4 → ℤ)',a);rv=re.findall(r'  !\[([^\n]+)\]',context[a:b]);assert len(rv)==1
names=rv[0].split(',');nv=re.findall(r'^  !\[([^\n]+)\]$',res,re.M);assert len(names)==22 and len(nv)==1 and names==nv[0].split(',')
for j,n in enumerate(names):assert f'theorem residual{j:02d}' in bridge and f'h{j:02d} := residual{j:02d} p v' in bridge
for name in ('signed_shift_cancel','w_cancel','d_cancel','v_cancel','evaluation_identity_candidate','evaluationIdentity_candidate','native_equivalence','standard_equivalence','reference_equivalence'):
 assert 'theorem '+name in bridge
assert 'theorem native_equivalence (h : EvaluationIdentity)' in bridge and 'IPRAAQ34Native.bridge34' in bridge and 'positiveShift\n  (AdaptiveAQ34Literal.literal CurrentWindowCarry2011.ports)' in endpoint
print(json.dumps({'scope':'source-only exact 3-rule DAG cancellation and bounded bridge statement checks; no Lean or provider authentication','parent_rows':len(old['source']),'child_rows':len(new['source']),'matched_parent_row_DAGs':len(old['source']),'canceled_pairs':len(pairs),'residual_proofs_proposed':len(names),'all_port_identity_lean_unelaborated':True,'endpoint_identity_premise_explicit':True},sort_keys=True,indent=2))
