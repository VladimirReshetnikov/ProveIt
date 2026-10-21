from pathlib import Path
import json,math
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();D=args.out;D.mkdir(parents=True,exist_ok=True)
if not __debug__:raise RuntimeError('Assertions must be enabled')
def up(n):
 q=(math.isqrt(8*n+1)-1)//2;y=n-q*(q+1)//2
 return q-y,y

def word(n):
 a,y=up(n)
 if a==0:c='S';r=y
 elif a==1:c='MP';r=up(y)[1]
 else:c='AX';r=up(up(y)[1])[1]
 return [c]+(word(r-1)if r else[])

balance=0;low=0;records=[];witness=None
for n in range(32):
 initial=balance;events=['FORCED_S']+word(n);prefix=[]
 for i,c in enumerate(events):
  balance+=10 if c=='AX'else 0 if c=='MP'else -1
  prefix.append(balance)
  if balance<low:low=balance;witness=dict(candidate=n,event_index=i,event=c)
 records.append(dict(candidate=n,entry_balance=initial,events=events,prefix_balances=prefix,exit_balance=balance))
assert low==-7
counts=[];total=0
for n in range(200000):
 a,y=up(n)
 if a==0:r=y;v=1
 elif a==1:r=up(y)[1];v=0
 else:r=up(up(y)[1])[1];v=0
 if r:v+=counts[r-1]
 counts.append(v);total+=v
 assert total<=n+1
out=dict(status='FORCED_TRANSFER_FINITE_BASE_PASS',required_candidates=[0,31],minimum_balance=low,witness=witness,exit_balance=balance,records=records,corroboration=dict(candidates=len(counts),total_S=total,scope='Corroboration only; infinite theorem proved separately.'))
(D/'FORCED_TRANSFER_CREDIT_BASE.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items()if k!='records'})
