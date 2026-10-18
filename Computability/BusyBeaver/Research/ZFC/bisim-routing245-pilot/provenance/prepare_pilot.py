#!/usr/bin/env python3
"""Emit the full pinned certificate plus seven source-only finite pilot checks.
No supplied imports, segment evaluation, compiler, checker or guard execution.
"""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
INPUT=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-register_bisimulation.json'
EXPECTED='228eb4833868bd8e48b8c35a1bc5af96db2fba742c583df4b8fde8e2daf68c1f'
PILOT=[0,90,103,329,791,3012]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def make(out):
 assert out.is_absolute() and not out.is_relative_to(ROOT) and not out.exists()
 assert sha(INPUT)==EXPECTED
 raw=json.loads(INPUT.read_text());assert set(raw)=={'start_pair','entries'} and raw['start_pair']==0
 entries=raw['entries'];assert len(entries)==3013
 adapted=[]
 for i,(a,b,j,k)in enumerate(entries):
  assert type(a)is str and type(b)is str and set(a+b)<={'0','1'} and max(len(a),len(b))<=128
  if j is None or k is None:
   assert i==90 and j is None and k is None;j=k=0
  else:assert type(j)is int and type(k)is int and 0<=j<3013 and 0<=k<3013
  adapted.append((int('1'+a,2),int('1'+b,2),j,k))
 assert len({tuple(e[:2])for e in entries})==3013
 blocks=[(lo,min(lo+32,3013))for lo in range(0,3013,32)]
 def node(lo,hi):
  if hi-lo==1:return '.leaf ('+', '.join(map(str,adapted[lo]))+')'
  mid=(lo+hi)//2
  return f'.branch {mid-lo} ({node(lo,mid)}) ({node(mid,hi)})'
 def top(lo,hi):
  if hi-lo==1:return f'chunk{lo:03}'
  mid=(lo+hi)//2;cut=sum(b-a for a,b in blocks[lo:mid])
  return f'.branch {cut} ({top(lo,mid)}) ({top(mid,hi)})'
 text='''import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.ProgramRouting245

/-!
Source-bisimulation pilot for the exact Routing245 logical decoder.
The full delivered 3013-pair certificate is preserved in balanced chunks.
Only the initial segment and entries0,90,103,329,791,3012 are checked here.
This unit does not prove allC, arbitrary-register halting equivalence,
binary-machine simulation or a PA consistency endpoint.

RMBisim.segFuel remains1000; the delivered Python default100000 is not assumed
to establish this bound. Each finite proof below uses the maintained checker.
Original benchmark/calculus: Mira-Cult; verification: Jeff Ketchersid;
compiler framework: Andrew James Wade. New routing/certificate provenance is
submission8286787dd0, maintained intake164/source68.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Pilot
open RegisterPath RMBisim

'''
 for i,(lo,hi)in enumerate(blocks):text+=f'-- Exact delivered indices [{lo}, {hi}).\nprivate def chunk{i:03} : CTree :=\n  {node(lo,hi)}\n\n'
 text+='''/-- Entire certificate in original order; all branch cuts are left sizes. -/
def cert : CTree :=
  '''+top(0,len(blocks))+'''

/-- Read an actual indexed entry of the full certificate before checking it. -/
def checkAt (i : Nat) : Bool :=
  match lookupC cert i with
  | some e => entryOk ActualTree254.tree TreeRouting245.tree cert e
  | none => false

/-- Initial segment only; this does not discharge the global allC obligation. -/
theorem initial_ok :
    branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true := by
  decide +kernel

'''
 for i in PILOT:text+=f'theorem entry{i:04}_ok : checkAt {i} = true := by\n  decide +kernel\n\n'
 text+='end SetTheory.BusyBeaver.ZFC.BisimRouting245Pilot\n'
 audit='''import BusyBeaver.ZFC.BisimRouting245Pilot

/-! Seven finite pilot clients only. No complete-bisimulation claim. -/
open SetTheory.BusyBeaver.ZFC
open RMBisim BisimRouting245Pilot
#print axioms BisimRouting245Pilot.initial_ok
'''
 for i in PILOT:audit+=f'#print axioms BisimRouting245Pilot.entry{i:04}_ok\n'
 audit+='''
example : branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true := initial_ok
'''
 for i in PILOT:audit+=f'example : checkAt {i} = true := entry{i:04}_ok\n'
 # Independent rendered CTree parser: recover all3013 tuples, cuts and indices.
 def parse(s,defs):
  tokens=re.findall(r'\.branch|\.leaf|chunk\d{3}|\d+|[(),]',s)
  assert ''.join(tokens)==re.sub(r'\s+','',s)
  n=0
  def consume(w):
   nonlocal n
   assert tokens[n]==w;n+=1
  def expr():
   nonlocal n
   w=tokens[n];n+=1
   if w=='(':
    z=expr();consume(')');return z
   if w.startswith('chunk'):return defs[w]
   if w=='.leaf':
    consume('(');vals=[]
    for j in range(4):
     vals.append(int(tokens[n]));n+=1
     if j<3:consume(',')
    consume(')');return ('leaf',tuple(vals))
   assert w=='.branch';cut=int(tokens[n]);n+=1
   return ('branch',cut,expr(),expr())
  tree=expr();assert n==len(tokens);return tree
 def flatten(t):
  if t[0]=='leaf':return [t[1]]
  left=flatten(t[2]);right=flatten(t[3]);assert t[1]==len(left);return left+right
 defs={}
 for m in re.finditer(r'private def (chunk\d{3}) : CTree :=\n  (.*)\n',text):defs[m[1]]=parse(m[2],defs)
 assert len(defs)==95
 body=re.search(r'def cert : CTree :=\n  (.*)\n',text)[1];tree=parse(body,defs)
 assert flatten(tree)==adapted
 def lookup(t,i):
  if t[0]=='leaf':return t[1]
  return lookup(t[2],i)if i<t[1]else lookup(t[3],i-t[1])
 assert all(lookup(tree,i)==adapted[i]for i in range(3013))
 assert [int(i)for i in re.findall(r'theorem entry\d+_ok : checkAt (\d+)',text)]==PILOT
 assert audit.count('#print axioms ')==7 and audit.count('\nexample ')==7
 out.mkdir(parents=True)
 for name,data in [('BisimRouting245Pilot.lean',text),('Audit.lean',audit)]: (out/name).write_text(data)
 inv={'status':'SOURCE_ONLY_PILOT_NOT_COMPILED','source':desc(out/'BisimRouting245Pilot.lean'),'audit':desc(out/'Audit.lean'),'emitter':desc(Path(__file__)),'certificate':desc(INPUT),'full_certificate_pairs':3013,'full_decrement_pair_count':3012,'full_halt_pair_index':90,'full_successor_references':6024,'chunk_sizes':[b-a for a,b in blocks],'pilot_indices':PILOT,'initial_segment_check':True,'named_probes':7,'typed_callers':7,'all3013_rendered_entries_exact':True,'every_cut_is_exact_left_size':True,'all3013_rendered_lookup_positions_exact':True,'halt_null_adaptation':'Only row90 null/null becomes0/0; checker ignores these halt successors.','scope':'Seven partial finite checks against full certificate, no allC theorem or halting equivalence.','lean_segment_fuel':1000,'delivered_python_default_fuel':100000,'segment_fuel_sufficiency':'No claim before actual checks; these pilot checks would cover only their selected branches.','proof_limits':'default','decider':'decide +kernel','source_imports':['BusyBeaver.ZFC.ActualTree254','BusyBeaver.ZFC.ProgramRouting245'],'compiler_execution':False,'supplied_code_execution':False,'segment_execution':False,'guard_execution':False}
 (out/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n');print(json.dumps(inv,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();make(a.output.resolve())
