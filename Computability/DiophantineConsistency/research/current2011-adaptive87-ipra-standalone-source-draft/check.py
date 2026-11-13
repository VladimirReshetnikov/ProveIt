#!/usr/bin/env python3
"""Read-only exact source-row, local algebra and endpoint-interface checks."""
import ast,gzip,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
def need(b,m):
 if not b:raise RuntimeError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
pins=json.loads((here/'pins.json').read_bytes())
for path,h in pins.items():need(sha((root/path).read_bytes())==h,'pin '+path)
def read(p):return (root/p).read_text()
g88=json.loads(read('research/adaptive-current13-metrics/polynomial.json'));g87=json.loads(read('research/adaptive-first-root-factor87/candidate.json'))
need(g88['witnesses']==g87['witnesses'] and g88['fixed_numerals']==g87['fixed_numerals'],'coordinate/port order')
need(g87['witnesses']==['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma'],'witness order')
def check_literal(path,start,end,g):
 s=read(path).split(start,1)[1].split(end,1)[0];lines=[x.strip() for x in s.splitlines() if x.strip()]
 headers=[f'let {v} : Expr (Fin 13) := .var {i}' for i,v in enumerate(g['witnesses'])]+[f'let {n} : Expr (Fin 13) := .constant (p {i})' for i,n in enumerate(g['fixed_numerals'])]
 need(lines[:17]==headers and lines[-1]==g['output'],'literal headers/output '+path)
 ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
 def leaf(x):
  if isinstance(x,ast.Name):return x.id
  if isinstance(x,ast.Constant) and type(x.value)==int:return x.value
  raise RuntimeError('unsupported literal operand')
 rows=[]
 for line in lines[17:-1]:
  need(line.startswith('let ') and ' := ' in line,'literal row '+line)
  name,rhs=line[4:].split(' := ',1);a=ast.parse(rhs,mode='eval').body
  need(isinstance(a,ast.BinOp) and type(a.op) in ops,'literal operation '+line)
  rows.append([name,ops[type(a.op)],leaf(a.left),leaf(a.right)])
 need(rows==g['source'],'literal rows '+path)
 return len(rows)
n88=check_literal('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean','def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) :=','\ndef expression :',g88)
n87=check_literal('Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean','def expressionAt87 (p : Fin 4 → ℤ) : Expr (Fin 13) :=','\ntheorem maintained_as_context',g87)
need(n88==88 and n87==87 and g88['source'][:20]==g87['source'][:20] and g88['source'][36:]==g87['source'][35:],'common cut')
need(g88['source'][20:36]==g87['removed_rows'] and g87['source'][20:35]==g87['replacement_rows'],'changed block')
known=set(g87['witnesses']+g87['fixed_numerals']);rows={}
for out,op,a,b in g87['source']:
 need(out not in known and op in ('+','-','*') and all(type(x)==int or x in known for x in (a,b)),'topology')
 rows[out]=(a,b);known.add(out)
seen=set();leaves=set();todo=[g87['output']]
while todo:
 n=todo.pop()
 if n in rows and n not in seen:seen.add(n);todo.extend(x for x in rows[n] if isinstance(x,str))
 elif n not in rows:leaves.add(n)
need(len(seen)==87 and set(g87['witnesses']+g87['fixed_numerals'])<=leaves,'liveness')
counts={op:sum(row[1]==op for row in g87['source']) for op in ('*','+','-')}
need(counts=={'*':47,'+':22,'-':18},'operation census')
# Prove local old/new root identity in Z[q3,qm,k,Bt,g31,Y].
def add(x,y,sign=1):
 z=x.copy()
 for m,v in y.items():z[m]=z.get(m,0)+sign*v
 return {m:v for m,v in z.items() if v}
def mul(x,y):
 z={}
 for a,u in x.items():
  for b,v in y.items():
   m=tuple(i+j for i,j in zip(a,b));z[m]=z.get(m,0)+u*v
 return {m:v for m,v in z.items() if v}
vars=[{tuple(int(i==j) for i in range(6)):1} for j in range(6)]
q3,qm,k,Bt,g31,Y=vars;one={(0,0,0,0,0,0):1};M=mul(q3,qm)
old=add(add(mul(M,g31),mul(Y,qm)),mul(Bt,mul(add(one,mul(k,qm)),q3)),-1)
new=add(add(mul(M,add(g31,mul(k,Bt),-1)),mul(Y,qm)),mul(Bt,q3),-1)
need(old==new,'ring root identity')
# Authenticate the existing full 2011 tuple payloads; their relation to Lean
# constants and the degree certificate is separate retained external evidence.
ports={};base=root/'research/adaptive-current13-metrics/coefficients'
for name,m in g88['coefficient_binding']['ports'].items():
 packed=(base/m['file']).read_bytes();raw=gzip.decompress(packed)
 need(sha(packed)==m['gzip_sha256'] and sha(raw)==m['raw_sha256'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==m['bits'],'port '+name)
 ports[name]=len(raw)
need(sum(ports.values())==47313,'total ports')
cert=json.loads(read('research/adaptive-current13-metrics/CERTIFICATE.json'))
need(cert['graph_pin']['sha256']==pins['research/adaptive-current13-metrics/polynomial.json'] and cert['degree']['exact_degree']==51 and cert['degree']['selected_coefficient']=='-32*beta^15','parent degree evidence')
s=read('research/current2011-adaptive87-ipra-standalone-source-draft/Adaptive87IPRAStandalone.lean.src');old=read('Lean/DiophantineConsistency/IPRAAdaptiveNativeZFC.lean');trans=read('Lean/DiophantineConsistency/IPRA87TranslatedRefutation.lean')
need(s.split('def noZero87 :',1)[1].split('\n\n',1)[0]==old.split('def noZero87 :',1)[1].split('\n\n',1)[0],'exact no-zero definition')
need('IPRA87TranslatedRefutation.translated_refutation' in s and 'IPRABoundedRhoZFC.zfcEquiv' in s and 'IPRAEquationComposition.equationComparison noZero87' in s,'native composition')
need('AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1' in trans and 'AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2' in trans,'translated operands')
need('import DiophantineConsistency.IPRA86TranslatedRefutation' not in s and 'import DiophantineConsistency.IPRAAdaptiveNativeZFC' not in s,'unwanted direct 86 import')
need('(IPRAStandardTheory.provable_iff _).2 native_equivalence87' in s,'standard direction')
meta=json.loads(read('reviews/pra87-translated-preliminary/metadata.json'))
need(meta['status']=='PRELIMINARY_COMPILED','historical status')
for name in ('HAAdaptiveFactor87','PRA87ZFCStrict','IPRA87TranslatedRefutation'):
 need(meta['source_objects'][name]['source_sha256']==pins['Lean/DiophantineConsistency/'+name+'.lean'],'historical source '+name)
print(json.dumps({'pins_sha256':sha((here/'pins.json').read_bytes()),'literal_rows_88':n88,'literal_rows_87':n87,'operation_counts':counts,'exact_root_ring_identity':True,'all_87_rows_live':True,'parent_degree_certificate':51,'coefficient_raw_bytes':sum(ports.values()),'identical_prior_nozero87_definition':True,'three_preliminary_source_hashes_match':True,'no_direct_86_client_import':True,'scope':'external source/graph checks and unelaborated endpoint proposal; no Lean/provider authentication'},sort_keys=True,indent=2))
