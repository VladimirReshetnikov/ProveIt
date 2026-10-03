#!/usr/bin/env python3
"""Verify all five original replay runs against every literal compiled guard.
Requires the unchanged sibling source directory; never writes into it.
"""
import hashlib,json,sys
from math import lcm
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE=Path(sys.argv[1]) if len(sys.argv)>1 else HERE.parent/'conservative-signal-frontend-20261002'
CODE=SOURCE/'code' if (SOURCE/'code'/'instantiate_morita.py').exists() else SOURCE
MACHINE=SOURCE/'data'/'MORITA_18_SIGNAL_MACHINE.json' if (SOURCE/'data'/'MORITA_18_SIGNAL_MACHINE.json').exists() else SOURCE/'MORITA_18_SIGNAL_MACHINE.json'
sys.path.insert(0,str(CODE));sys.path.insert(0,str(HERE))
from compile_packet import Compiler
import instantiate_morita as original
C=Compiler().close();lookup={(s,J):r for r,(s,t,J) in enumerate(C.branches)}
base_event=original.event;counts=dict(events=0,simultaneous_events=0,strict_guards=0,equality_guards=0,zero_input_gaps=0);used=set()
def event(conf,speed,rules,**kwargs):
 result=base_event(conf,speed,rules,**kwargs)
 if result is None:return result
 out,dt,rec=result
 m=bytes(C.ids[a] for _,a in conf);s=C.seen[m];J=tuple(rec['J']);r=lookup[s,J];_,t,_=C.branches[r]
 assert bytes(C.ids[a] for _,a in out)==C.modes[t]
 g=[conf[i+1][0]-conf[i][0] for i in range(17)];scale=lcm(*(x.denominator for x in g));h=[int(x*scale) for x in g]
 X=h+[C.codes[s]*sum(h)];eq,st=C.guards(s,t,J)
 assert all(sum(v*X[i] for i,v in row)==0 for _,row in eq)
 slack=[sum(v*X[i] for i,v in row)-1 for _,row in st];assert all(x>=0 for x in slack)
 Y=[sum(v*X[i] for i,v in row) for row in C.matrix(s,t,J)]
 assert all(Y[i]==scale*rec['pivot_speed']*(out[i+1][0]-out[i][0]) for i in range(17))
 assert Y[17]==C.codes[t]*sum(Y[:17])
 assert dt==g[J[0]]/C.cs[s][J[0]]
 counts['events']+=1;counts['simultaneous_events']+=len(J)>1;counts['strict_guards']+=len(st);counts['equality_guards']+=len(eq);counts['zero_input_gaps']+=sum(x==0 for x in h);used.add(r)
 return result
original.event=event
runs=[]
for productions,word in [(('YN','YYN'),'NYY'),(('YN','YYN'),'Y'),(('YN','YYN'),''),((),'N'),(('',),'NY')]:
 receipt=original.signal_replay(productions,word);runs.append(receipt)
 print(json.dumps(dict(input=word,batches=receipt['signal_batches'],tm_steps=receipt['source_tm_steps'],halt_kind=receipt['halt_kind'])),flush=True)
report=dict(status='PASS',scope='All five original complete runs, every event, exact integer guards and branch maps',counts=counts,distinct_branches_used=len(used),replays=runs,source_machine_sha256=hashlib.sha256(MACHINE.read_bytes()).hexdigest())
(HERE/'ORIGINAL_REPLAY_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status='PASS',counts=counts,distinct_branches_used=len(used))),flush=True)
