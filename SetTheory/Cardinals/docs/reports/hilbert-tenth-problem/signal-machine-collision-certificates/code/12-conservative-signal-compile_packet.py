#!/usr/bin/env python3
"""Exact bounded-memory compiler for the literal 18-particle event graph.

No floating point, LP, sampled depth, identity completion, or extra scale.
Run: python compile_packet.py build [--residuals]
     python compile_packet.py residuals --output residuals.jsonl.gz
     python compile_packet.py coefficient I [J]  (J absent: linear term)
The fully expanded polynomial has >10^12 monomials: use its literal sparse
residual circuit, not an accidental dense expansion. See PROOF_AND_LEDGER.md.
"""
import argparse, gzip, hashlib, json, os, struct, time
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'MORITA_18_SIGNAL_MACHINE.json'
N=18; D=18; GAPS=17; CAP=500000

def dump(o):return json.dumps(o,separators=(',',':'))
def write_json(path,o):path.write_text(json.dumps(o,indent=2)+'\n')
def sha(path):
 h=hashlib.sha256()
 with open(path,'rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def compressed(path):return gzip.open(path,'wt',encoding='utf-8',compresslevel=6)

class Compiler:
 def __init__(self):
  self.machine=json.loads(SOURCE.read_text());self.labels=sorted(self.machine['meta_signals'])
  self.ids={s:i for i,s in enumerate(self.labels)}
  self.speed=[self.machine['meta_signals'][s] for s in self.labels]
  assert len(self.labels)==114 and self.machine['population']==N
  self.rules={}
  for r in self.machine['collision_rules']:
   inp=tuple(sorted((self.ids[s] for s in r['incoming']),key=lambda a:-self.speed[a]))
   out=tuple(sorted((self.ids[s] for s in r['outgoing']),key=lambda a:self.speed[a]))
   assert len(inp)==len(out)==2 and self.speed[inp[0]]>self.speed[inp[1]] and self.speed[out[0]]<self.speed[out[1]]
   assert inp not in self.rules;self.rules[inp]=out
  assert len(self.rules)==445
  self.initial=bytes(self.ids[s] for s in self.machine['mode_encoding']['label_orders']['initial'])
 def eligible(self,m):return [i for i in range(GAPS) if (m[i],m[i+1]) in self.rules]
 def successors(self,m):
  e=self.eligible(m)
  for mask in range(1,1<<len(e)):
   J=tuple(e[k] for k in range(len(e)) if mask>>k&1)
   if any(b==a+1 for a,b in zip(J,J[1:])):continue
   out=bytearray(m)
   for i in J:out[i:i+2]=bytes(self.rules[(m[i],m[i+1])])
   yield J,bytes(out)
 def code(self,m):
  q=0
  for a in m:q=114*q+a
  return q+1
 def close(self):
  modes=[self.initial];seen={self.initial:0};branches=[];depth=[0]
  cursor=0
  while cursor<len(modes):
   m=modes[cursor]
   for J,out in self.successors(m):
    if out not in seen:
     if len(modes)>=CAP:raise RuntimeError(f'Closure cap {CAP} reached; no completion claimed')
     seen[out]=len(modes);modes.append(out);depth.append(depth[cursor]+1)
    branches.append((cursor,seen[out],J))
   cursor+=1
  self.modes=modes;self.seen=seen;self.branches=branches;self.depth=depth
  self.codes=[self.code(m) for m in modes]
  self.cs=[tuple(self.speed[m[i]]-self.speed[m[i+1]] for i in range(GAPS)) for m in modes]
  self.B=len(branches);self.copy_base=36+self.B;self.slack_base=36+19*self.B
  self.offsets=[];T=0
  for s,t,J in branches:
   self.offsets.append(T);T+=sum(c>=0 for c in self.cs[s])+19-len(J)
  self.T=T;self.V=self.slack_base+T
  return self
 def copy(self,r,i):return self.copy_base+18*r+i
 def selector(self,r):return 36+r
 def matrix(self,s,t,J):
  c=self.cs[s];j=J[0];cj=c[j];q=self.codes[t];rows=[]
  for i in range(GAPS):
   row={i:cj};row[j]=row.get(j,0)-c[i]
   rows.append(sorted((k,v) for k,v in row.items() if v))
  rows.append([(i,q*(cj-(sum(c) if i==j else 0))) for i in range(GAPS) if cj-(sum(c) if i==j else 0)])
  return rows
 def guards(self,s,t,J):
  c=self.cs[s];j=J[0];cj=c[j];q=self.codes[s]
  equal=[('mode',[(i,-q) for i in range(GAPS)]+[(17,1)])]
  for i in J[1:]:equal.append((f'tie:{i}',sorted([(i,cj),(j,-c[i])])))
  strict=[(f'germ:{i}',[(i,1)]) for i in range(GAPS) if c[i]>=0]
  strict += [('span',[(i,1) for i in range(GAPS)]),('positive_delay',[(j,1)])]
  for i in range(GAPS):
   if i not in J:
    strict.append((f'first:{i}',sorted([(i,cj)]+([(j,-c[i])] if c[i] else []))))
  return equal,strict
 def branch_record(self,r):
  s,t,J=self.branches[r];eq,st=self.guards(s,t,J)
  return dict(id=r,source=s,target=t,J=list(J),pivot=J[0],pivot_speed=self.cs[s][J[0]],
      matrix=[[[i,str(v)] for i,v in row] for row in self.matrix(s,t,J)],
      equality=[dict(name=n,terms=[[i,str(v)] for i,v in row]) for n,row in eq],
      strict=[dict(name=n,terms=[[i,str(v)] for i,v in row],slack=self.slack_base+self.offsets[r]+k) for k,(n,row) in enumerate(st)],
      selector=self.selector(r),copy_start=self.copy(r,0))
 def incidence(self,var):
  """All affine residual coefficients incident to one variable; O(B) worst case."""
  if not 0<=var<self.V:raise ValueError('Variable outside packet')
  if var<18:return {1+var:1}
  if var<36:return {19+var-18:1}
  if var<self.copy_base:
   r=var-36; eq,st=self.guards(*self.branches[r]);base=self.local_row_start(r)
   return {0:1,**{base+len(eq)+k:-1 for k in range(len(st))}}
  if var<self.slack_base:
   r,i=divmod(var-self.copy_base,18);s,t,J=self.branches[r]
   ans={1+i:-1}
   for k,row in enumerate(self.matrix(s,t,J)):
    for ix,v in row:
     if ix==i:ans[19+k]=-v
   eq,st=self.guards(s,t,J);base=self.local_row_start(r)
   for k,(_,row) in enumerate(eq+st):
    for ix,v in row:
     if ix==i:ans[base+k]=v
   return ans
  from bisect import bisect_right
  off=var-self.slack_base;r=bisect_right(self.offsets,off)-1
  eq,_=self.guards(*self.branches[r]);return {self.local_row_start(r)+len(eq)+off-self.offsets[r]:-1}
 def local_row_start(self,r):
  # Every branch contributes |J| equalities; compute prefix only on demand.
  if not hasattr(self,'rowstarts'):
   self.rowstarts=[];n=37
   for s,t,J in self.branches:
    self.rowstarts.append(n);n+=len(J)+sum(c>=0 for c in self.cs[s])+19-len(J)
  return self.rowstarts[r]
 def coefficient(self,i,j=None):
  if i==-1 and j is None:return 1
  if j is None:return -2 if 36<=i<self.copy_base else 0
  if i>j:i,j=j,i
  a,b=self.incidence(i),self.incidence(j)
  result=sum(v*b.get(k,0) for k,v in a.items())*(1 if i==j else 2)
  # Complementarity contributes b_s * copy_(r,k) iff s != r.
  if 36<=i<self.copy_base and self.copy_base<=j<self.slack_base:
   if i-36!=(j-self.copy_base)//18:result+=1
  return result

def emit_row(f,rowid,const,terms):
 f.write('{"id":'+str(rowid)+',"constant":"'+str(const)+'","terms":[')
 first=True
 for i,v in terms:
  if not v:continue
  if not first:f.write(',')
  first=False;f.write('['+str(i)+',"'+str(v)+'"]')
 f.write(']}\n')

def export_residuals(C,path):
 """Full literal sparse coefficient list of every squared affine residual."""
 with compressed(path) as f:
  emit_row(f,0,-1,((C.selector(r),1) for r in range(C.B)))
  for i in range(D):emit_row(f,1+i,0,iter([(i,1)]+[(C.copy(r,i),-1) for r in range(C.B)]))
  for k in range(D):
   def output_terms():
    yield 18+k,1
    for r,(s,t,J) in enumerate(C.branches):
     for i,v in C.matrix(s,t,J)[k]:yield C.copy(r,i),-v
   emit_row(f,19+k,0,output_terms())
  rowid=37
  for r,(s,t,J) in enumerate(C.branches):
   eq,st=C.guards(s,t,J)
   for _,terms in eq:
    emit_row(f,rowid,0,((C.copy(r,i),v) for i,v in terms));rowid+=1
   for k,(_,terms) in enumerate(st):
    terms=[(C.selector(r),-1)]+[(C.copy(r,i),v) for i,v in terms]+[(C.slack_base+C.offsets[r]+k,-1)]
    emit_row(f,rowid,0,terms);rowid+=1
 return rowid

def export_expanded(C,path):
 """Every distinct monomial once, O(B+T) working memory, no dense Gram matrix.

 Output records [i,j,coefficient] represent z_i*z_j; i=-1 denotes the
 implicit constant coordinate 1. Grouped order, not global lexical order.
 Never called by build: the actual packet has >10^12 nonzero monomials.
 """
 meta=[]
 for s,t,J in C.branches:
  c=C.cs[s];p=J[0];a=c[p];meta.append((p,a,c,a*C.codes[t],C.codes[s]))
 def dot(r,i,s,j):
  p,a,c,_,_=meta[r];q,b,d,_,_=meta[s]
  if i!=p and j!=q:return a*b if i==j else 0
  if i!=p:return -a*d[i] if i!=q else 0
  if j!=q:return -b*c[j] if j!=p else 0
  return sum(c[k]*d[k] for k in range(17) if k!=p and k!=q)
 count=0
 with compressed(path) as f:
  def emit(i,j,v):
   nonlocal count
   assert v!=0
   if i>j:i,j=j,i
   f.write('['+str(i)+','+str(j)+',"'+str(v)+'"]\n');count+=1
  emit(-1,-1,1)
  for r in range(C.B):emit(-1,C.selector(r),-2)
  H=17*C.B
  for a in range(H):
   r,i=divmod(a,17);p,cj,c,w,qo=meta[r]
   for b in range(a,H):
    s,j=divmod(b,17);nd=dot(r,i,s,j)
    g=w*meta[s][3]+nd+int(i==j)
    if r==s:g+=qo*qo+1+nd+int(i==j and c[i]>=0)+int(i==j and i==p)
    emit(C.copy(r,i),C.copy(s,j),g*(1 if a==b else 2))
  for r in range(C.B):
   for s in range(r,C.B):emit(C.copy(r,17),C.copy(s,17),2)
   for i in range(17):emit(C.copy(r,i),C.copy(r,17),-2*meta[r][4])
  for i in range(36):emit(i,i,1)
  for r,(s,t,J) in enumerate(C.branches):
   for i in range(18):emit(i,C.copy(r,i),-2)
   for k,row in enumerate(C.matrix(s,t,J)):
    for i,v in row:emit(18+k,C.copy(r,i),-2*v)
  for r in range(C.B):
   Tr=(C.offsets[r+1] if r+1<C.B else C.T)-C.offsets[r]
   for s in range(r,C.B):emit(C.selector(r),C.selector(s),1+Tr if r==s else 2)
   for s in range(C.B):
    if r!=s:
     for i in range(18):emit(C.selector(r),C.copy(s,i),1)
   eq,st=C.guards(*C.branches[r]);total=[0]*18
   for k,(_,row) in enumerate(st):
    slack=C.slack_base+C.offsets[r]+k
    emit(C.selector(r),slack,2);emit(slack,slack,1)
    for i,v in row:total[i]+=v;emit(C.copy(r,i),slack,-2*v)
   for i,v in enumerate(total):
    if v:emit(C.selector(r),C.copy(r,i),-2*v)
 return count

def verify_compact(C):
 """Read-only exhaustive comparison of archived finite data with fresh closure."""
 with gzip.open(HERE/'MODES.jsonl.gz','rt') as f:
  count=0
  for i,line in enumerate(f):
   row=json.loads(line);assert row==dict(id=i,labels=list(C.modes[i]),q=str(C.codes[i]),c=list(C.cs[i]),bfs_depth=C.depth[i]);count+=1
  assert count==len(C.modes)
 with gzip.open(HERE/'EVENTS.jsonl.gz','rt') as f:
  count=0
  for r,line in enumerate(f):
   source,target,J=C.branches[r];assert json.loads(line)==[r,source,target,J[0],sum(1<<j for j in J)];count+=1
  assert count==C.B
 ledger=json.loads((HERE/'LEDGER.json').read_text())
 assert ledger['source_sha256']==sha(SOURCE) and ledger['modes']==len(C.modes) and ledger['branches']==C.B
 E=T=entries=0
 for source,target,J in C.branches:
  eq,st=C.guards(source,target,J);E+=len(eq);T+=len(st)
  c=C.cs[source];h=[ci if i in J else max(ci,0)+1 for i,ci in enumerate(c)];X=h+[C.codes[source]*sum(h)]
  assert all(sum(v*X[i] for i,v in row)==0 for _,row in eq)
  assert all(sum(v*X[i] for i,v in row)>0 for _,row in st)
 assert E==ledger['equality_guards'] and T==ledger['strict_guards']
 return dict(status='PASS',modes=len(C.modes),branches=C.B,equality_guards=E,strict_guards=T,all_compact_records_and_branch_witnesses_checked=True)

def build(C,residuals=False):
 t0=time.time();E=T=L=MN=NG=0;maxQ=0;maxmat=0;maxaff=0
 Gdist=Counter();Jdist=Counter();pdist=Counter();endpoint=Counter();maxdense=(0,None)
 for r,(s,t,J) in enumerate(C.branches):
  c=C.cs[s];j=J[0];cj=c[j];q=C.codes[s];qn=C.codes[t]
  assert sum(c)==0, 'Active endpoints stationary is checked, not presumed for all modes'
  eq,st=C.guards(s,t,J);M=C.matrix(s,t,J)
  E+=len(eq);T+=len(st);L+=sum(len(row) for _,row in st)
  NG+=sum(len(row) for row in M[:17]);MN+=sum(len(row) for row in M)
  Gdist[sum(ci>=0 for ci in c)]+=1;Jdist[len(J)]+=1;pdist[cj]+=1
  maxmat=max(maxmat,max(abs(v) for row in M for _,v in row));maxaff=max(maxaff,maxmat,q)
  # Constructive exact witness: tau=1, all initial gaps strictly positive.
  h=[ci if i in J else max(ci,0)+1 for i,ci in enumerate(c)];X=h+[q*sum(h)]
  assert all(sum(v*X[i] for i,v in row)==0 for _,row in eq)
  assert all(sum(v*X[i] for i,v in row)>0 for _,row in st)
  Y=[sum(v*X[i] for i,v in row) for row in M]
  assert {i for i,v in enumerate(Y[:17]) if v==0}==set(J)
  assert all(v>=0 for v in Y) and Y[17]==qn*sum(Y[:17])
  out=C.modes[t];assert all(Y[i]>0 or C.speed[out[i]]<C.speed[out[i+1]] for i in range(17))
  # Exact maximum among local gap-gap off-diagonal coefficients.
  candidate=2*((cj*qn)**2+q*q+1+2*cj*max(0,-min(c)))
  if candidate>maxdense[0]:maxdense=(candidate,r)
 H=17*C.B
 quad=H*(H+1)//2 + C.B*(C.B+1)//2 + 17*C.B +36+18*C.B+MN + C.B*(C.B+1)//2 +18*C.B*(C.B-1)+17*C.B+T+L+T
 nonzero=1+C.B+quad
 # All cross-branch gap-gap coefficients <= 2*maxmat^2+19586, strictly smaller.
 assert maxdense[0]>2*maxmat*maxmat+19586
 assert T==C.T
 modespath=HERE/'MODES.jsonl.gz';branchpath=HERE/'BRANCHES.jsonl.gz'
 with compressed(modespath) as f:
  for i,m in enumerate(C.modes):
   f.write(dump(dict(id=i,labels=list(m),q=str(C.codes[i]),c=list(C.cs[i]),bfs_depth=C.depth[i]))+'\n')
 with compressed(branchpath) as f:
  for r in range(C.B):f.write(dump(C.branch_record(r))+'\n')
 (HERE/'MODES.bin').write_bytes(b''.join(C.modes))
 with compressed(HERE/'EVENTS.jsonl.gz') as f:
  for r,(s,t,J) in enumerate(C.branches):f.write(dump([r,s,t,J[0],sum(1<<j for j in J)])+'\n')
 with open(HERE/'EVENTS.bin','wb') as f:
  for s,t,J in C.branches:f.write(struct.pack('<III',s,t,sum(1<<j for j in J)))
 terminal_ids={k:C.seen[bytes(C.ids[s] for s in v)] for k,v in C.machine['mode_encoding']['label_orders'].items()}
 ledger=dict(status='complete_least_mode_only_closure',source_sha256=sha(SOURCE),labels=114,population=18,state_dimension=18,modes=len(C.modes),branches=C.B,max_bfs_depth=max(C.depth),
  eligible_edges_by_mode=dict(Counter(len(C.eligible(m)) for m in C.modes)),simultaneous_branch_sizes=dict(Jdist),pivot_speed_distribution=dict(pdist),germ_strict_guards_distribution=dict(Gdist),
  collision_free_modes=sum(all(ci<=0 for ci in c) for c in C.cs),no_eligible_edge_modes=sum(not C.eligible(m) for m in C.modes),terminal_mode_ids=terminal_ids,
  equality_guards=E,strict_guards=T,weak_guards=0,strict_form_nonzeros=L,
  auxiliary_variables=19*C.B+T,total_variables=C.V,affine_residuals=37+E+T,complementarity_products=C.B,
  affine_variable_nonzeros=35*C.B+36+MN+2*E+L+2*T,affine_constant_nonzeros=1,
  gap_matrix_nonzeros_total=NG,full_matrix_nonzeros_total=MN,
  max_gap_matrix_abs=24,max_mode_code=str(max(C.codes)),max_mode_code_bits=max(C.codes).bit_length(),
  max_affine_abs=str(maxaff),max_affine_bits=maxaff.bit_length(),max_matrix_abs=str(maxmat),
  expanded_constant_terms=1,expanded_linear_nonzeros=C.B,expanded_quadratic_nonzeros=quad,expanded_total_nonzeros=nonzero,
  expanded_max_abs_coefficient=str(maxdense[0]),expanded_max_coefficient_bits=maxdense[0].bit_length(),expanded_max_branch_id=maxdense[1],
  exact_branch_witnesses_checked=C.B,elapsed_export_seconds=round(time.time()-t0,3))
 write_json(HERE/'LEDGER.json',ledger)
 circuit=dict(format='sparse-affine-squares-plus-factored-complementarity-v1',domain='nonnegative integers',degree=2,
  variable_order=dict(X=[0,18],Y=[18,36],selectors=[36,C.copy_base],copies=[C.copy_base,C.slack_base],slacks=[C.slack_base,C.V]),
  interval_convention='half-open; branch r copy starts copy_base+18*r; all coefficients serialized as exact decimal strings',
  polynomial='sum(row_value**2 for row in RESIDUALS) + sum((selector_sum-b_r)*copy_sum_r for r)',
  shared_expressions=dict(selector_sum={'op':'sum','variables':[36,C.copy_base]},copy_sum_r={'op':'sum','variables':'copy_base+18*r .. copy_base+18*r+17'}),
  selector_sum_is_expression_not_auxiliary=True,other_selector_sum_is_nonnegative_on_all_naturals=True,
  residual_export_command='python compile_packet.py residuals --output RESIDUALS.jsonl.gz',coefficient_query_command='python compile_packet.py coefficient I J',
  closure='MODES.jsonl.gz',branches='EVENTS.jsonl.gz',event_record_format=['branch_id','source_mode_id','target_mode_id','pivot','J_bitmask'],optional_verbose_branches='BRANCHES.jsonl.gz',reconstruction='compile_packet.py: Compiler.close, guards, matrix, export_residuals',ledger='LEDGER.json',guard_semantics='equalities=0; strict forms>=1; coordinate nonnegativity is the ambient domain')
 write_json(HERE/'POLYNOMIAL_CIRCUIT.json',circuit)
 if residuals:
  count=export_residuals(C,HERE/'RESIDUALS.jsonl.gz');assert count==ledger['affine_residuals']
 manifest={p.name:dict(bytes=p.stat().st_size,sha256=sha(p)) for p in HERE.iterdir() if p.is_file() and p.name in ['MORITA_18_SIGNAL_MACHINE.json','MODES.jsonl.gz','MODES.bin','BRANCHES.jsonl.gz','LEDGER.json','POLYNOMIAL_CIRCUIT.json','RESIDUALS.jsonl.gz','compile_packet.py','EVENTS.bin','EVENTS.jsonl.gz','PROOF_AND_LEDGER.md','check_original_replays.py','ORIGINAL_REPLAY_AUDIT.json','test_exporter.py','EXPORTER_TEST_RECEIPT.json']}
 write_json(HERE/'MANIFEST.json',manifest)
 print(json.dumps(ledger,indent=2),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['build','verify','residuals','coefficient','expanded']);p.add_argument('indices',nargs='*',type=int);p.add_argument('--output',default='RESIDUALS.jsonl.gz');p.add_argument('--residuals',action='store_true');p.add_argument('--allow-trillion-terms',action='store_true');args=p.parse_args()
 C=Compiler().close()
 if args.command=='build':build(C,args.residuals)
 elif args.command=='verify':print(json.dumps(verify_compact(C)))
 elif args.command=='residuals':print(export_residuals(C,Path(args.output)))
 elif args.command=='expanded':
  if not args.allow_trillion_terms:p.error('This exports >10^12 terms. Supply --allow-trillion-terms only with a deliberate storage/time budget.')
  print(export_expanded(C,Path(args.output)))
 else:print(C.coefficient(*args.indices))
