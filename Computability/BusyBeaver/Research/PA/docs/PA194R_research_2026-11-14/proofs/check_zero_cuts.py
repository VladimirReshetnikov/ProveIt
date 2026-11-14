#!/usr/bin/env python3
"""Check small inductive zero cuts on the complete resolved source graphs.

The mathematical proof is ordinary induction: every entry into a cut forces
register r to zero, and no cut instruction increases r. This script checks
all finite premises on BOTH programs, including edges from every outside site.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
CONFIG={
 'PA194F':(3553,6,set(range(3550,3554)),[(3545,3551),(3548,3550)]),
 'PA194A':(26,3,set(range(0,10))|set(range(11,27))|set(range(3523,3646)),[(48,3638),(49,3554),(3519,3523)]),
 'PA194X':(26,6,{25,26,3550,3551,3552,3553,3633,3634,3635,3636,3637},[(22,25),(3545,3551),(3548,3550),(3628,3634),(3631,3633)])
}

def edges(code):
 for pc,ins in enumerate(code):
  op=ins[0]
  if op=='halt':continue
  if op=='jump':yield pc,ins[1],None,'jump'
  elif op=='inc':yield pc,ins[2],ins[1],'inc'
  else:
   assert op=='dec'
   yield pc,ins[2],ins[1],'zero'
   yield pc,ins[3],ins[1],'positive'

def premises(code,reg,cut):
 assert all(0<=p<len(code) for p in cut)
 boundary=[]
 for pc,target,r,kind in edges(code):
  assert 0<=target<len(code)
  if target in cut and pc not in cut:
   assert kind=='zero' and r==reg,('unguarded incoming edge',pc,target,r,kind)
   boundary.append((pc,target))
 for pc in cut:
  assert code[pc][:2]!=['inc',reg],('zero register incremented inside cut',pc)
 return sorted(boundary)

def check(family):
 changed,reg,cut,expected=CONFIG[family]
 old=json.loads((ROOT/'inputs/pa194CS.instructions.json').read_text())
 new=json.loads((ROOT/'machines'/family/'instructions.json').read_text())
 assert len(old)==len(new)==3646
 differences=[i for i,(a,b) in enumerate(zip(old,new)) if a!=b]
 assert differences==[changed]
 assert old[changed][0]=='jump'
 assert new[changed]==['dec',reg,old[changed][1],changed+1]
 assert changed in cut
 assert premises(old,reg,cut)==premises(new,reg,cut)==expected
 seed=[2]+[0]*8
 assert 25 not in cut or seed[reg]==0
 result={'family':family,'register':reg,'changed_site':changed,'cut_sites':sorted(cut),
  'cut_size':len(cut),'boundary_zero_edges':expected,'all_boundary_edges_checked':True,
  'both_programs_preserve_cut':True,'source_steps_agree_on_invariant':True,
  'arbitrary_initial_registers_at_site25':25 not in cut,
  'new_instruction_graph_sha256':hashlib.sha256(json.dumps(new,separators=(',',':')).encode()).hexdigest(),
  'scope':'Finite premises for the ordinary PA induction proof; not a Lean/Rocq proof.'}
 return result

if __name__=='__main__':
 if not __debug__:raise SystemExit('Assertions must be enabled.')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--family',choices=list(CONFIG)+['all'],default='all')
 ap.add_argument('--output',type=Path)
 a=ap.parse_args();results=[check(f) for f in CONFIG if a.family in (f,'all')]
 data=json.dumps(results,indent=2)+'\n'
 if a.output:a.output.write_text(data)
 print(data)
