#!/usr/bin/env python3
"""Exact all-tape, one-step quotient proof for native65→98."""
from pathlib import Path
import argparse,hashlib,json

def read(p):
 t={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  assert(q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R')
  t[q,b]=(w,1 if d=='R'else-1,z)
 states={q for q,b in t}
 assert set(t)=={(q,b)for q in states for b in(0,1)}and{z for w,d,z in t.values()}-states=={230}
 assert start==0 and 0 in states
 return t

def prove(old_path,new_path):
 old,new=read(old_path),read(new_path);phi=lambda q:98 if q==65 else q
 assert set(q for q,b in old)==set(q for q,b in new)|{65}
 assert 65 not in{q for q,b in new} and 98 in{q for q,b in new}
 assert old[65,0]==old[98,0]==(0,1,19)
 assert old[65,1]==old[98,1]==(1,1,114)
 assert new=={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=65}
 checks=[]
 for(q,b),(w,d,z)in sorted(old.items()):
  assert new[phi(q),b]==(w,d,phi(z))
  checks.append({'old_row':[q,b,w,d,z],'new_row':[phi(q),b,w,d,phi(z)]})
 assert len(checks)==454 and len(new)==452 and phi(0)==0 and phi(230)==230
 return {'status':'EXACT_ALL_TAPE_ONE_STEP_QUOTIENT_PASS','old_working_states':227,'new_working_states':226,
 'start':0,'halt':230,'deleted':65,'retained':98,'checked_old_rows':454,'old_steps_per_block':1,'new_steps_per_block':1,
 'old_sha256':hashlib.sha256(old_path.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(new_path.read_bytes()).hexdigest(),
 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'row_proofs':checks,
 'scope':'For every binary tape, integer head position and old working control, one old step equals one new step after applying65→98 to the control, with exactly the same complete tape and head. The map fixes the initial and halt controls and maps no working control to halt; deterministic induction gives identical halting times from corresponding configurations.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();j=prove(a.old,a.new);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(j,indent=2)+'\n');print(j['status'],j['checked_old_rows'],'rows')
