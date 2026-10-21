#!/usr/bin/env python3
"""Replay two exact complete-interface failures of weak equality.

Neither fixture is asserted to occur on the machine's blank run.  The second
fixture has the scratch values of the genuine AX(1,3,0,0) command; its result
register is set to zero to keep the literal finite witness small.  The gate
does not touch this register on this accepting path, so its cache corruption
is independent of that value.
"""
import argparse,csv,hashlib,json
from pathlib import Path
import finite_frames as n

HERE=Path(__file__).resolve().parent
PREFIX='111010010011101111'
BASE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
FIXTURES=[
 {'name':'gate_counterexample','registers':[0,1,0,0,2,0,2,2,0],
  'parameters':{'a':2,'b':0,'c':2},'observed_register':1,
  'status':'EXACT_VALID_INTERFACE_FRESHNESS_GATE_COUNTEREXAMPLE',
  'scope':'Complete valid first-comparison interface with putative result register1=1. Baseline rejects and clears1; weak218 accepts and preserves1. This falsifies contextual interchangeability. This result value is not asserted to be produced by the AX constructor, and this frame is not asserted reachable from blank.'},
 {'name':'cache_forge_counterexample','registers':[0,0,0,0,3,0,1,1,0],
  'parameters':{'a':3,'b':0,'c':1},'observed_register':5,
  'status':'EXACT_VALID_INTERFACE_CACHED_ONE_FORGERY',
  'scope':'Complete valid first-comparison interface, with scratch values of AX(c=1,a=3,b=0,u=0), but result register1=0 for a small literal witness. Both gates accept. Baseline leaves cache5=0; weak218 leaves cache5=1. The accepting gate path preserves register1, so this corruption also holds for the actual AX output value. No reachability from the blank run is asserted.'}
]

def read_table(raw):
 t={}
 for line in raw.decode('ascii').splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,m,z=line.split();key=(int(q),int(b));assert key not in t
  t[key]=(int(w),1 if m=='R'else-1,int(z))
 return t

def decode(q,h,ones,rows):
 if not n.dispatch(q,h,ones):return None
 for site in rows:
  pc=site[0]
  if all((h+i in ones)==(bit=='1')for i,bit in enumerate(pc)):
   if any(x in ones for x in range(h+len(pc),h+52)):return None
   header=min(x for x in ones if x>=h+64);p=header+1;vals=[]
   while p<=max(ones):
    assert p not in ones and p+1 in ones;p+=1;start=p
    while p in ones:p+=1
    vals.append(p-start-1)
   return {'site':site,'logical_registers':[vals[j]for j in n.PHY],
           'gap':header-h-64,'spares':vals[9:]}
 return None

def run(table,rows,registers):
 first=next(x for x in rows if x[0].startswith(PREFIX+'000'))
 ones=n.frame(first[0],registers,[0]);q=84;h=0;trace=[];dispatches=[]
 initial=sorted(ones)
 for tick in range(100000):
  if q==84:
   d=decode(q,h,ones,rows)
   if d:
    dispatches.append({'tick':tick,'head':h,**d})
    if tick and not d['site'][0].startswith(PREFIX):
     return(q,h,ones),trace,dispatches,first,initial
  assert q!=254
  bit=int(h in ones);w,m,z=table[q,bit]
  trace.append((tick,q,h,bit,w,m,z))
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=m
 raise RuntimeError('finite counterexample did not reach gate exit')

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--baseline219',type=Path,required=True)
 ap.add_argument('--output',type=Path,default=HERE/'weak218_rejected')
 args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 baseline=args.baseline219/'machine/k219.native.tm'
 assert hashlib.sha256(baseline.read_bytes()).hexdigest()==BASE_SHA
 out=[]
 for fixture in FIXTURES:
  reports=[]
  for label,tp,sp in [
   ('baseline219',baseline,args.baseline219/'machine/sites219.json'),
   ('weak218',HERE/'weak218_rejected/machine.native.tm',HERE/'weak218_rejected/sites.json')]:
   raw=tp.read_bytes();table=read_table(raw);rows=json.loads(sp.read_text())
   config,tr,ds,first,initial=run(table,rows,fixture['registers'])
   trace_name=label+'_'+fixture['name']+'_trace.csv'
   path=args.output/trace_name
   with path.open('w',newline='')as f:
    w=csv.writer(f);w.writerow(['tick','state','head','read','write','move','target']);w.writerows(tr)
   reports.append({'name':label,'table_sha256':hashlib.sha256(raw).hexdigest(),
     'initial_site':first,'initial_registers':fixture['registers'],'initial_spares':[0],
     'initial_state':84,'initial_head':0,'initial_one_cells':initial,
     'steps':len(tr),'dispatches':ds,'final_state':config[0],'final_head':config[1],
     'final_one_cells':sorted(config[2]),'all_other_cells':0,
     'trace_csv':trace_name,'trace_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
  reg=fixture['observed_register']
  assert reports[0]['dispatches'][-1]['logical_registers'][reg]==0
  assert reports[1]['dispatches'][-1]['logical_registers'][reg]==1
  report={k:v for k,v in fixture.items()if k not in ['name','registers']}
  report['runs']=reports
  (args.output/(fixture['name']+'.json')).write_text(json.dumps(report,indent=2)+'\n')
  out.append({'name':fixture['name'],'observed_register':reg,
    'runs':[{'name':r['name'],'steps':r['steps'],
     'exit_registers':r['dispatches'][-1]['logical_registers']}for r in reports]})
 print(json.dumps(out,indent=2))

if __name__=='__main__':main()
