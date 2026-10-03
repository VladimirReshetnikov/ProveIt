#!/usr/bin/env python3
"""Bounded independent complete-polynomial/paid-ledger audit; no producer suites."""
import argparse,hashlib,itertools,json,sys,types
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
SOURCE_PIN='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'
RECEIPT_PIN='e13858da0f3385fe25ea719364f8fbf3fe9367893571972fbd3d8d0db82ec203'
def sha(b):return hashlib.sha256(b).hexdigest()
def require(v,m):
 if not v:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def plus(p,q,sign=1):
 o=p.copy()
 for m,v in q.items():o[m]=o.get(m,0)+sign*v
 return {m:v for m,v in o.items() if v}
def mult(p,q):
 o={}
 for m,v in p.items():
  for n,w in q.items():
   k=tuple(sorted(m+n));require(len(k)<=2,'Every actual gate is at most quadratic');o[k]=o.get(k,0)+v*w
 return {m:v for m,v in o.items() if v}
def load(source):
 b=Path(source).read_bytes();require(sha(b)==SOURCE_PIN,'Candidate before import')
 m=types.ModuleType('_independent_three_mass_emitter_subject');m.__file__=str(Path(source).resolve());sys.modules[m.__name__]=m
 exec(compile(b,m.__file__,'exec'),m.__dict__);return m
def original_polynomials(cert,packet):
 names=packet['variables'];indices={x:i for i,x in enumerate(names)};require(len(indices)==len(names),'Unique coordinates')
 forward=cert.get('forward_certificate',cert)
 pair={r['u']:(r['e'],'v'+r['u'][1:]) for step in forward['steps'] for r in step}
 def affine(f):
  p={}
  for name,c in f.items():
   require(type(c)is int,'Exact original coefficient')
   if name=='':p=plus(p,{():c})
   elif packet['coordinate']=='mass' and name in pair:
    e,v=pair[name];p=plus(p,{(indices[v],):c,(indices[e],):-c})
   else:p=plus(p,{(indices[name],):c})
  return p
 rows=[affine(r['affine']) for r in cert['squares']]
 gate_groups=[];B=len(forward['branches'])
 for t,step in enumerate(forward['steps']):
  p={}
  for product in cert['products'][t*B:(t+1)*B]:p=plus(p,mult(affine(product['left']),affine(product['right'])))
  gate_groups.append(p)
 full={}
 for p in rows:full=plus(full,mult(p,p))
 for p in gate_groups:full=plus(full,p)
 return indices,rows,gate_groups,full

def check_packet(cert,p):
 idx,rows,groups,want=original_polynomials(cert,p)
 env={name:{(i,):1} for name,i in idx.items()};deps={};counts=Counter()
 def atom(x):
  if type(x)is str:
   require(x in env,'Topological closure');return env[x]
  require(type(x)is int,'Exact literal');return {():x} if x else {}
 for node in p['source']:
  require(type(node)is list and len(node)==4,'Binary paid gate')
  r,op,x,y=node;require(type(r)is str and r not in env,'Fresh gate');require(op in ('+','-','*'),'Gate operation')
  a,b=atom(x),atom(y);env[r]=mult(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
  counts[op]+=1;deps[r]=[z for z in (x,y) if type(z)is str and z in deps]
 require(atom(p['output'])==want,'Entire coefficient polynomial')
 require(max(map(len,want),default=0)==2,'Exact final degree two')
 require(len(rows)==len(p['ports']['squares']),'No missing row port')
 for old,(label,reg),row in zip(cert['squares'],p['ports']['squares'],rows):require(label==old['label'] and atom(reg)==row,'Each literal affine residual')
 require(len(groups)==len(p['ports']['inactive_sums']),'Every step gate sum')
 for reg,poly in zip(p['ports']['inactive_sums'],groups):require(atom(reg)==poly,'Each whole inactive sum')
 require(atom(p['ports']['N0'])=={():1,(idx['x'],):1},'Paid ordinary loader')
 live=set()
 def visit(reg):
  if reg in deps and reg not in live:
   live.add(reg)
   for d in deps[reg]:visit(d)
 visit(p['output'])
 require(live==set(deps),'No dead charged gates')
 ledger={'M':counts['*'],'A':counts['+']+counts['-'],'total':len(deps)}
 require(exact(ledger,p['ledger']),'Independent operation count')
 require(p['natural_witnesses']==2*p['horizon']*p['branch_count'],'Core witness slots')
 return {'ledger':ledger,'affine_rows':len(rows),'inactive_step_sums':len(groups),'gates':len(deps)}

def fixture(C,CT,name,h,clean,clock_variant=False):
 I=C.Instruction;M=C.Machine
 if name=='incdec':m=M(('s','q','h'),'h',(I('s','q','inc',0),I('q','h','dec',0)))
 elif name.startswith('incchain'):
  k=int(name[8:]);states=tuple('q'+str(i) for i in range(k+1));m=M(states,states[-1],tuple(I(states[i],states[i+1],'inc',0) for i in range(k)))
 elif name in ('dec2','zero3','test3'):
  op='dec' if name=='dec2' else 'zero';c=0 if name=='dec2' else 1
  ins=[I('s','h',op,c)]
  if name=='test3':ins.append(I('s','h','positive',1))
  m=M(('s','h'),'h',tuple(ins))
 elif name=='empty':m=M(('s',),'s',())
 else:raise ValueError(name)
 if clean:return CT.export_clean_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'T'},model='phase-radius-one' if clock_variant else 'native')
 return C.export_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'},clock_scale=4 if clock_variant else 1)

def run(source,receipt,repo):
 S=load(source);b=Path(receipt).read_bytes();require(sha(b)==RECEIPT_PIN,'Author receipt pin');saved=json.loads(b)
 sources,archives=S.source_bytes(repo);counts=Counter();cases=[]
 with S.subjects(sources) as (C,CT):
  for row in saved['cases']:
   name,h,clean=row['fixture'],row['horizon'],row['cleaned_exact_target'];cert=fixture(C,CT,name,h,clean)
   require(sha(json.dumps(cert,sort_keys=True,separators=(',',':')).encode())==row['certificate_sha256'],'Actual full exported source pin')
   ledgers={}
   for coord,inactive in itertools.product(('literal','offset','mass'),('direct','factored')):
    packet=S.emit(cert,coord,inactive);a=check_packet(cert,packet);key=coord+'_'+inactive;ledgers[key]=a['ledger']
    require(exact(a['ledger'],row['ledgers'][key]),'Saved complete ledger')
    if row['full_packets'] is not None:require(exact(packet,row['full_packets'][key]),'Saved full source')
    counts['whole_polynomial_identities']+=1;counts['affine_residual_identities']+=a['affine_rows'];counts['inactive_group_identities']+=a['inactive_step_sums'];counts['live_paid_gates']+=a['gates']
   for inactive in ('direct','factored'):
    a,b=ledgers['offset_'+inactive],ledgers['mass_'+inactive]
    require(a['M']==b['M'] and a['A']-b['A']==h*len(cert.get('forward_certificate',cert)['branches']),'Matched Bh; no missing intermediates');counts['matched_Bh_checks']+=1
   cases.append({'fixture':name,'horizon':h,'clean':clean,'best_old':min(v['total'] for k,v in ledgers.items() if not k.startswith('mass')),'best_mass':min(v['total'] for k,v in ledgers.items() if k.startswith('mass')),'ledgers':ledgers})
  empty=C.Machine(('s',),'s',())
  excluded=[C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'x'}),
            CT.export_clean_certificate(empty,'s',0,{'mode':'free_raw','name':'x'})]
  for name in ('g0','u_7_0'):
   excluded.append(C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'x'},
                   {'mode':'free','name':name},{'mode':'free','name':'T'}))
  excluded.append(C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'z'},
                  {'mode':'free','name':'y'},{'mode':'free','name':'T'}))
  for cert in excluded:
   try:S.emit(cert)
   except ValueError:counts['unsupported_valid_interfaces_rejected']+=1
   else:raise ValueError('Bounded interface guard missing')
  # Independently paid overall clock scaling in both actual source compilers.
  for clean in (False,True):
   cert=fixture(C,CT,'incdec',2,clean,True)
   for coord,inactive in itertools.product(('literal','offset','mass'),('direct','factored')):
    check_packet(cert,S.emit(cert,coord,inactive));counts['scale_four_whole_identities']+=1
 return {'candidate_sha256':SOURCE_PIN,'author_receipt_sha256':RECEIPT_PIN,'archives':archives,'counts':dict(counts),'cases':cases,'scope':'Complete emitted free_raw-x native y/T and compact-clean T schedules; original source math proof reviewed separately; no author suite or global optimization claim'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--receipt',required=True);p.add_argument('--repo',required=True);p.add_argument('--output');p.add_argument('--expect');a=p.parse_args();r=run(a.source,a.receipt,a.repo)
 if a.expect:require(exact(r,json.loads(Path(a.expect).read_text())),'Exact saved review receipt')
 if a.output:Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(r['counts'],sort_keys=True))
