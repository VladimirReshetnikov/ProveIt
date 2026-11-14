#!/usr/bin/env python3
"""Exact AX11-to-AX11H source splice, checked with two CFG resolvers.
This is a finite syntactic certificate, not a PA calibration theorem.
"""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'verification/reference'))
import check_ax11_source as parent

def read_rows(path):
 result={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,n=line.split();result[int(q),int(b)]=[int(w),d,int(n)]
 return result

def check(machine):
 inherited=parent.bind(ROOT/'inputs/ax11')
 old=json.loads((ROOT/'inputs/ax11/instructions.json').read_text())
 old_nodes=json.loads((ROOT/'inputs/ax11/nodes.json').read_text())
 nodes=json.loads((machine/'nodes.json').read_text())
 expected_nodes=dict(old_nodes)
 expected_nodes['node170']=[['node36',['node167','node145']],'node57']
 assert nodes==expected_nodes
 grammar=json.loads((machine/'grammar.tree.json').read_text())
 base=parent.gram(ROOT/'inputs/primary.grammar.json')
 def transform(t):
  if t==('leaf','breakTo',1):return 'node49'
  return tuple(transform(x)for x in t)if isinstance(t,tuple)and len(t)==2 else t
 assert parent.tup(grammar)==transform(base)
 sites=[]
 def visit(t,path):
  if isinstance(t,str):return visit(grammar if t=='x67'else nodes[t],path)
  if t[0]=='leaf':sites.append([path,t[1],t[2]]);return
  assert len(t)==2
  visit(t[0],path+'0');visit(t[1],path+'1')
 visit('node172','')
 assert sites==json.loads((machine/'sites.json').read_text())
 graph=parent.graph(sites)
 assert graph==json.loads((machine/'instructions.json').read_text())
 removed=3661
 assert old[removed]==['inc',6,3662]
 assert old[3660]==['dec',1,3663,3661] and old[3662]==['jump',3660]
 assert len(old)==3672 and len(graph)==3671
 def relocate(i):return i-int(i>removed)
 for i,ins in enumerate(old):
  if i==removed:continue
  k=2 if ins[0]in('inc','dec')else 1
  expected=ins[:k]+[relocate(j)for j in ins[k:]]
  assert expected==graph[relocate(i)],(i,expected,graph[relocate(i)])
 assert graph[3660:3662]==[['dec',1,3662,3661],['jump',3660]]
 old_rows=read_rows(ROOT/'inputs/ax11/machine.native.tm')
 new_rows=read_rows(machine/'machine.native.tm')
 edits=[[q,b,old_rows[q,b],new_rows[q,b]]for q,b in sorted(old_rows)if old_rows[q,b]!=new_rows[q,b]]
 assert len(edits)==5
 assert {tuple(x[:2])for x in edits}=={(38,0),(38,1),(214,0),(214,1),(312,0)}
 return dict(status='PASS',family='PA194AX11H',old_sites=len(old),new_sites=len(graph),
  inherited_AX11_splices=inherited['resolved_edges_preserved_modulo_two_splices'],
  removed_site=removed,removed_instruction=old[removed],
  retained_instructions_exactly_relocated=len(graph),
  sole_change='Delete X increment while erasing visible top T before Shift',
  independent_source_resolvers_agree=True,native_edits_from_AX11=edits,
  meaning='The T-to-X transfer loop becomes T-clear; the H-to-T/X copy is unchanged.',
  machine_sha256=hashlib.sha256((machine/'machine.tm').read_bytes()).hexdigest(),
  calibration_claimed=False)

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--machine',type=Path,default=ROOT/'machine')
 p.add_argument('--output',type=Path,required=True)
 a=p.parse_args();r=check(a.machine)
 a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
