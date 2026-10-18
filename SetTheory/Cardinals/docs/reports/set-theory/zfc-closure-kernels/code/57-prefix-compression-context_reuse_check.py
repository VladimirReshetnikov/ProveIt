#!/usr/bin/env python3
"""Conditional guard checker for takeover of old state2 by the new scanner."""
from pathlib import Path
from collections import Counter
import sys,json,argparse
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'redesign'))
import mp_protocol_runtime as m
m.generate();audit=m.audit
parser=argparse.ArgumentParser()
parser.add_argument('--table')
args=parser.parse_args()
directory=ROOT/'compression/prefix_best_native'
base=audit.read_table(Path(args.table).read_bytes()) if args.table else audit.read_table((directory/'table.tm').read_bytes())
T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in base.items()}
if not args.table:
 for b in (0,1):del T['85',b]
 for q,b,target in ((75,1,2),(2,1,97),(0,1,4),(42,1,6),(20,0,6),(20,1,6),(143,1,6)):
  w,d,t=T[str(q),b];T[str(q),b]=w,d,str(target)
ns={'__name__':'strict_reuse'};exec((directory/'strict_prefix_decrement.py').read_text(),ns)
oldoracle=ns['oracle']
def oracle(q,branch,state):
 answer=oldoracle(q,branch,state)
 if answer and state==('plain',None) and q in ns['SKIP']:return '6',answer[1]
 return answer
ns['oracle']=oracle
for line in (directory/'native_cases.txt').read_text().splitlines():
 v=line.split();i=int(v[0]);pc=v[1];branch=(int(v[2]),bool(int(v[3]))) if int(v[2])>=0 else None
 nxt=v[4];overflow=int(v[5]);effect=int(v[6]);r=int(v[7]);halt=bool(int(v[8]))
 eff=('inc' if effect==0 else 'dec',r) if effect>=0 else None
 target=([] if nxt=='-' else [('b',int(x)) for x in nxt])+[('r',0,1,43+overflow+(effect==1)-(0 if nxt=='-' else len(nxt))),('b',1),('box',('plain',eff))]
 try:ns['run'](T,pc,branch,ns['canon']([('b',1)],target),halt=halt,fuel=1000)
 except Exception as ex:print('FAIL',i,pc,branch,ex);break
else:print('ALL 8366 CONDITIONAL GUARDS PASS')
