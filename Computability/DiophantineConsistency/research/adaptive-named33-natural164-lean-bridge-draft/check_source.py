#!/usr/bin/env python3
"""Read-only exact four-rule DAG cancellation and source checks; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','9c917b1ecf75e4754a8bfcecb0651bd4fd8de4c143138cd7b73eeb9305b28daa')
obs=json.loads(pin(P/'result.json','c94ab0be06276e0cc7503e3a6c0beada1e47cf3746cf139a3e7b2f41e097b809'))
old=json.loads(pin(D/'research/adaptive-square-sums33/candidate.json','a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735'))
new=json.loads(pin(D/'research/adaptive-named33-natural164-signed-cancel/candidate.json','b42bb4501265b3dfac592b74d0950b79c322064d3febe38aeec56e741112e121'))
oldsrc=pin(D/'Lean/DiophantineConsistency/AdaptiveNamedValues33.lean','0c6bde076f2cc77e2d4d08f7542abb6bf469b6062e0ab7d1276250da1b06abbb')
endpoint=pin(D/'Lean/DiophantineConsistency/IPRANamedValues33Native.lean','c6c072f16c436d8e4608753684f1afceda523b2789c33ff4c192e5fdb624f8ce')
src={n:pin(P/n,h) for n,h in obs['source_hashes'].items()};lit=src['Named33Natural164Literal.lean.src'];ores=src['Named33ParentResiduals.lean.src'];nres=src['Named33Natural164Residuals.lean.src'];bridge=src['Named33Natural164Bridge.lean.src']
start=oldsrc.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n');end=oldsrc.index('\ndef embed ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=']+[f'  let {n} : Expr (Fin 33) := .var ({i})' for i,n in enumerate(old['witnesses'])]+[f'  let {n} : Expr (Fin 33) := .constant (p {i})' for i,n in enumerate(old['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in old['source']]+['  '+old['output']]
assert oldsrc[start:end].splitlines()==expected and len(old['source'])==139
for i,n in enumerate(new['witnesses']):assert f'let {n} : Expr (Fin 33) := .var {i}' in lit
for i,n in enumerate(new['fixed_numerals']):assert f'let {n} : Expr (Fin 33) := .constant (p {i})' in lit
for n,o,a,b in new['source']:assert f'  let {n} := {a} {o} {b}\n' in lit
assert len(new['source'])==164 and len(new['witnesses'])==33
pairs={'namedBt':('wPositive','wNegative'),'Z':('zPositive','zNegative'),'Dstar':('dPositive','dNegative'),'V':('vPositive','vNegative')}
for n,(a,b) in pairs.items():
 assert [n,'-',a,b] in old['source'] and [r[0] for r in old['source'] if a in r[2:]]==[n] and [r[0] for r in old['source'] if b in r[2:]]==[n]
pool={};desc=[]
def intern(x):
 if x not in pool:pool[x]=len(desc);desc.append(x)
 return pool[x]
one=intern(('int',1));shared={n:intern(('input','n_'+n)) for n in old['witnesses']};ports={n:intern(('port',n)) for n in old['fixed_numerals']};parent={n:intern(('+',shared[n],one)) for n in old['witnesses']};parent.update(ports);child={n:shared[n[2:]] for n in new['witnesses']};child.update(ports)
def value(env,x):return intern(('int',x)) if type(x)==int else env[x]
for n,o,a,b in new['source']:child[n]=intern((o,value(child,a),value(child,b)))
for n,o,a,b in old['source']:
 x,y=value(parent,a),value(parent,b)
 if n in pairs:
  A,B=desc[x],desc[y];assert o=='-' and A[0]=='+' and B[0]=='+' and A[2]==B[2]==one;x,y=A[1],B[1]
 parent[n]=intern((o,x,y));assert parent[n]==child[n],n
assert parent[old['output']]==child[new['output']]
def vec(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
names=vec(ores);assert len(names)==20 and vec(nres)==names
for j,n in enumerate(names):assert f'theorem residual{j:02d}' in bridge and f'h{j:02d} := residual{j:02d} p v' in bridge
for name in ('signed_shift_cancel','w_cancel','z_cancel','d_cancel','v_cancel','evaluation_identity_candidate','evaluationIdentity_candidate','native_equivalence','standard_equivalence','reference_equivalence'):
 assert 'theorem '+name in bridge
assert 'theorem native_equivalence (h : EvaluationIdentity)' in bridge and 'IPRANamedValues33Native.bridge33' in bridge and 'positiveShift\n  (AdaptiveNamedValues33.literal CurrentWindowCarry2011.ports)' in endpoint
print(json.dumps({'scope':'source-only exact four-rule DAG cancellation and bounded bridge checks; no Lean or provider authentication','parent_rows':len(old['source']),'child_rows':len(new['source']),'matched_parent_row_DAGs':len(old['source']),'canceled_pairs':len(pairs),'residual_proofs_proposed':len(names),'all_port_identity_lean_unelaborated':True,'endpoint_identity_premise_explicit':True},sort_keys=True,indent=2))
