#!/usr/bin/env python3
"""Independent template, finite-execution and exact macro-count checks; no producer imports."""
import json,hashlib,argparse
from pathlib import Path
from collections import Counter
OUT=Path(__file__).resolve().parent
_parser=argparse.ArgumentParser(description=__doc__)
_default=OUT.parent
_parser.add_argument('--base',type=Path,default=_default,help='Root of the reset-net packet, containing source/ and shared-reset-arcs/.')
BASE=_parser.parse_args().base.resolve()
hashes={}
def read(path):
 b=path.read_bytes();hashes[str(path.relative_to(BASE))]=hashlib.sha256(b).hexdigest();return json.loads(b)
p=read(BASE/'two-counter/source/literal2.json');v=read(BASE/'two-counter/source/virtual3.json');cert=read(BASE/'two-counter/source/macro_certificates.json')['prime_macros']
net=read(BASE/'shared-reset-arcs/two-counter/reset_net.json');by={t['name']:t for t in net['transitions']}
rows=p['rows'];expected={};cut=p['virtual_cuts'];dest=lambda x:'HALT' if x=='HALT' else cut[x]
for c in cert:
 label=c['virtual_label'];op,register,*targets=v['rows'][label];prime=(2,3,5)[register];stem=c['prefix']
 assert (c['op'],c['prime'],c['destinations'])==(op,prime,targets)
 part={}
 if op=='ADD':
  part[stem+'drain']=['SUB',0,stem+'mul0',stem+'restore']
  for j in range(prime):part[stem+f'mul{j}']=['ADD',1,stem+f'mul{j+1}' if j+1<prime else stem+'drain']
  part[stem+'restore']=['SUB',1,stem+'put',dest(targets[0])];part[stem+'put']=['ADD',0,stem+'restore']
  assert cut[label]==stem+'drain'
 else:
  for j in range(prime):part[stem+f'rem{j}']=['SUB',0,stem+f'rem{j+1}' if j+1<prime else stem+'group',stem+f'r{j}_drain' if j else stem+'quo']
  part[stem+'group']=['ADD',1,stem+'rem0'];part[stem+'quo']=['SUB',1,stem+'qput',dest(targets[0])];part[stem+'qput']=['ADD',0,stem+'quo']
  for remainder in range(1,prime):
   root=stem+f'r{remainder}_';part[root+'drain']=['SUB',1,root+'put0',root+'tail0']
   for j in range(prime):part[root+f'put{j}']=['ADD',0,root+f'put{j+1}' if j+1<prime else root+'drain']
   for j in range(remainder):part[root+f'tail{j}']=['ADD',0,root+f'tail{j+1}' if j+1<remainder else dest(targets[1])]
  assert cut[label]==stem+'rem0'
 assert not expected.keys()&part.keys();expected.update(part)
assert expected==rows and len(rows)==8408
assert set(c['virtual_label'] for c in cert)==set(v['rows'])

def cost(op,prime,n):
 q,d=divmod(n,prime)
 if op=='ADD':return dict(final=prime*n,ADD=2*prime*n,pos=(prime+1)*n,zero=2,branch=0,peak=prime*n)
 if d==0:return dict(final=q,ADD=2*q,pos=n+q,zero=2,branch=0,peak=n)
 return dict(final=n,ADD=n+q,pos=n+q,zero=2,branch=1,peak=n)
def fire(name,m):
 t=by[name];assert all(m.get(x,0)>=n for x,n in t['pre'].items())
 for x,n in t['pre'].items():m[x]=m.get(x,0)-n
 assert not any(m.get(x,0) for x in t['reset'])
 for x in t['reset']:m[x]=0
 for x,n in t['post'].items():m[x]=m.get(x,0)+n
 return {x:n for x,n in m.items() if n}

stats=Counter();reps={}
def check_case(c,n):
 label=c['virtual_label'];op,register,*targets=v['rows'][label];prime=(2,3,5)[register];want=cost(op,prime,n);end=dest(targets[want['branch']]);pc=cut[label];regs=[n,0];counts=Counter();peak=n
 mass=max(n,want['peak']);m={'q:'+pc:1,'A':n,'reserve':mass-n,'budget':mass};m={k:x for k,x in m.items() if x};source_steps=shared_steps=0
 while True:
  op0,i,*dst=rows[pc];oldpc=pc
  if op0=='ADD':regs[i]+=1;pc=dst[0];counts['ADD']+=1;names=[oldpc+':inc']
  elif regs[i]:regs[i]-=1;pc=dst[0];counts['pos']+=1;names=[oldpc+':pos']
  else:pc=dst[1];counts['zero']+=1;names=[oldpc+':dispatch','shared_reset_'+p['registers'][i],oldpc+':return']
  peak=max(peak,sum(regs));source_steps+=1
  for name in names:m=fire(name,m);shared_steps+=1
  assert m.get('A',0)==regs[0] and m.get('B',0)==regs[1] and m.get('q:'+pc)==1
  assert not any(k.startswith('marker:') for k in m)
  assert m.get('budget',0)-m.get('reserve',0)==sum(regs)
  if pc==end and regs[1]==0:break
  assert source_steps<100000
 assert regs==[want['final'],0] and all(counts[k]==want[k] for k in ['ADD','pos','zero'])
 assert peak==want['peak'] and shared_steps==source_steps+4
 stats['cases']+=1;stats['source_steps']+=source_steps;stats['shared_steps']+=shared_steps
for c in cert:
 reps.setdefault((c['op'],c['prime']),c)
 for n in range(9):check_case(c,n)
for c in reps.values():
 for n in range(9,129):check_case(c,n)

# The enormous A64 run is accounted by closed-form macro costs, never enumerated.
label=v['entry'];registers=[6,0,0];n=64;M=64;tot=Counter();trace=[]
while label!='HALT':
 op,i,*targets=v['rows'][label];prime=(2,3,5)[i];want=cost(op,prime,n)
 branch=0 if op=='ADD' or registers[i]>0 else 1;assert branch==want['branch']
 trace.append(dict(virtual_step=len(trace),label=label,input_A=n,output_A=want['final'],ADD=want['ADD'],positive_SUB=want['pos'],zero_SUB=want['zero'],physical_instructions=want['ADD']+want['pos']+want['zero'],macro_peak=want['peak']))
 if op=='ADD':registers[i]+=1
 elif branch==0:registers[i]-=1
 n=want['final'];assert n==2**registers[0]*3**registers[1]*5**registers[2]
 label=targets[branch];M=max(M,want['peak'])
 for k in ['ADD','pos','zero']:tot[k]+=want[k]
 assert len(trace)<1000
h=sum(tot.values());Z=tot['zero'];F=n;minimum=h+2*Z+F+2*M-64+4
assert (h,Z,F,M,minimum)==(738579314485258247,656,177147,59604644775390625,857788604036217896)
assert tot['ADD']-tot['pos']==F-64
prod=read(BASE/'shared-reset-arcs/two-counter/accepting_macro_count_A64.json')
assert prod['physical_source_instructions']==h and prod['physical_SUB_zero']==Z and prod['shared_minimum_duration']==minimum
for a,b in zip(trace,prod['macro_steps']):
 for x,y in [('virtual_step','virtual_step'),('label','label'),('input_A','encoded_A_before'),('output_A','encoded_A_after'),('ADD','physical_ADD'),('positive_SUB','physical_SUB_positive'),('zero_SUB','physical_SUB_zero'),('physical_instructions','physical_instructions')]:assert a[x]==b[y]
assert len(prod['macro_steps'])==len(trace)==328
# Raw zero has no prime valuations; check its literal two-source-step/six-shared-step cycle.
zero_cycle=[]
for fuel in [0,1,7]:
 m={k:n for k,n in {'q:'+p['entry']:1,'reserve':fuel,'budget':fuel}.items() if n};initial=m.copy();pc=p['entry'];names=[]
 for step in range(2):
  op,i,*dst=rows[pc];assert op=='SUB';names += [pc+':dispatch','shared_reset_'+p['registers'][i],pc+':return'];pc=dst[1]
 for name in names:m=fire(name,m)
 assert pc==p['entry'] and m==initial;zero_cycle.append({'fuel':fuel,'shared_period':len(names),'word':names})
receipt=dict(status='passed',source_rows_reconstructed=len(expected),prime_macros=len(cert),finite_executions=dict(stats),finite_test_domain='Each of 528 macros at A=0..8, plus one representative of each of six (operation,prime) shapes at A=9..128; B=0 initially. Every physical instruction is expanded through the literal shared net.',A64=dict(virtual_steps=len(trace),physical_source_instructions=h,ADD=tot['ADD'],positive_SUB=tot['pos'],zero_SUB=Z,final_mass=F,peak_total_mass=M,minimum_fuel=M-64,minimum_shared_duration=minimum,full_physical_trace_enumerated=False,full_shared_trace_enumerated=False),raw_zero_cycles=zero_cycle,input_sha256=hashes)
(OUT/'prime_macro_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(OUT/'independent_A64_macro_trace.json').write_text(json.dumps(trace,indent=2)+'\n');print(json.dumps(receipt,indent=2))
