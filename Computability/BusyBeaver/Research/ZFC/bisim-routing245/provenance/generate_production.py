#!/usr/bin/env python3
"""Emit source-only exact certificate projections, independent chunks, or final join.
No compiler/checker/submission imports; root decides which stage to generate/run.
"""
from pathlib import Path
import argparse,hashlib,json,re
BASE=Path('/tmp/zfc-routing245-lean/source-bisim-production')
PILOT=Path('/tmp/zfc-routing245-lean/source-bisim-pilot/generated/BisimRouting245Pilot.lean')
CERT=Path('/home/codex/.codex/worktrees/ec20/Proofs/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-register_bisimulation.json')
PILOT_SHA='b7b061dffcdaddf856eabbf6a2cc826e22431bbbc74d0d9e8704167bbe1801b1'
CERT_SHA='228eb4833868bd8e48b8c35a1bc5af96db2fba742c583df4b8fde8e2daf68c1f'
NS='SetTheory.BusyBeaver.ZFC'
DATA='BisimRouting245Data'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
blocks=[(lo,min(lo+32,3013))for lo in range(0,3013,32)]
paths={}
def shape(lo,hi,path=''):
 if hi-lo==1:paths[lo]=path;return ('chunk',lo)
 mid=(lo+hi)//2;cut=sum(b-a for a,b in blocks[lo:mid])
 return ('branch',cut,shape(lo,mid,path+'L'),shape(mid,hi,path+'R'))
TREE=shape(0,len(blocks))
def cexpr(t,prefix=''):
 if t[0]=='chunk':return prefix+f'chunk{t[1]:03}'
 return f'.branch {t[1]} ({cexpr(t[2],prefix)}) ({cexpr(t[3],prefix)})'
def bexpr(t,f='f',prefix=''):
 if t[0]=='chunk':return f'(allC {f} {prefix}chunk{t[1]:03})'
 return f'({bexpr(t[2],f,prefix)} && {bexpr(t[3],f,prefix)})'
def projection(path):
 expr='cert'
 for bit in path:expr=f'{"leftPart" if bit=="L" else "rightPart"} ({expr})'
 return expr

def validate_inputs():
 assert sha(PILOT)==PILOT_SHA and sha(CERT)==CERT_SHA
 source=PILOT.read_text();top=re.search(r'def cert : CTree :=\n  (.*)\n',source)[1]
 assert top==cexpr(TREE)
 raw=json.loads(CERT.read_text());assert len(raw['entries'])==3013 and raw['start_pair']==0
 # Read actual pilot literals, independently from new projection rendering.
 defs={m[1]:m[2]for m in re.finditer(r'private def (chunk\d{3}) : CTree :=\n  (.*)\n',source)}
 assert len(defs)==95
 for i,(lo,hi)in enumerate(blocks):
  tuples=[tuple(map(int,m.groups()))for m in re.finditer(r'\.leaf \((\d+), (\d+), (\d+), (\d+)\)',defs[f'chunk{i:03}'])]
  expected=[]
  for a,b,nz,z in raw['entries'][lo:hi]:expected.append((int('1'+a,2),int('1'+b,2),0 if nz is None else nz,0 if z is None else z))
  assert tuples==expected
 # Each root-to-block projection locates exactly its intended structural leaf.
 for i,path in paths.items():
  t=TREE
  for bit in path:t=t[2]if bit=='L'else t[3]
  assert t==('chunk',i)
 return raw

def data_source():
 s=f'''import BusyBeaver.ZFC.BisimRouting245Pilot

/-!
Public structural blocks of the already checked pilot's complete certificate.
No certificate entry is copied or changed. Each block is a projection of the
public full certificate; cert_decomposition proves exact reassembly.
This unit supplies data identities and the passed initial-segment proof only.
The 95 block checks and final halting equivalence are separate units.
-/
set_option autoImplicit false
namespace {NS}.{DATA}
open RegisterPath RMBisim

def cert : CTree := BisimRouting245Pilot.cert

theorem cert_eq : cert = BisimRouting245Pilot.cert := rfl

private def leftPart : CTree → CTree
  | .branch _ l _ => l
  | _ => .empty

private def rightPart : CTree → CTree
  | .branch _ _ r => r
  | _ => .empty

'''
 for i,(lo,hi)in enumerate(blocks):s+=f'/-- Exact certificate indices [{lo}, {hi}); structural path {paths[i]}. -/\ndef chunk{i:03} : CTree := {projection(paths[i])}\n\n'
 s+='''/-- Balanced reassembly with the original left-subtree sizes. -/
def assembly : CTree :=
  '''+cexpr(TREE)+'''

/-- This identity prevents omissions, duplicated blocks, or empty projections. -/
theorem cert_decomposition : cert = assembly := rfl

/-- The checker relation always uses the full certificate for successor lookup. -/
def test : Entry → Bool := entryOk ActualTree254.tree TreeRouting245.tree cert

/-- Generic structural decomposition; no semantic entry checks are assumed. -/
theorem allC_decomposition (f : Entry → Bool) :
    allC f cert =
      '''+bexpr(TREE)+''' := by
  rw [cert_decomposition]
  rfl

/-- Reuse only the exact passed initial-segment theorem. -/
theorem initial_ok :
    branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true :=
  BisimRouting245Pilot.initial_ok

end '''+NS+'.'+DATA+'\n'
 return s

def data_audit():
 s=f'''import BusyBeaver.ZFC.{DATA}
open {NS}
open RegisterPath RMBisim {DATA}
#print axioms {DATA}.cert_eq
#print axioms {DATA}.cert_decomposition
#print axioms {DATA}.allC_decomposition
#print axioms {DATA}.initial_ok

example : cert = BisimRouting245Pilot.cert := cert_eq
example : cert = assembly := cert_decomposition
example (f : Entry → Bool) : allC f cert =
    '''+bexpr(TREE)+''' := allC_decomposition f
example : branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true := initial_ok
example (f : Entry → Bool) (h : allC f assembly = true) : allC f cert = true := by
  rw [cert_decomposition]
  exact h
'''
 return s

def chunk_source(i):
 lo,hi=blocks[i];mod=f'BisimRouting245Chunk{i:03}'
 return f'''import BusyBeaver.ZFC.{DATA}

/-! Exact certificate block [{lo}, {hi}); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace {NS}.{mod}
open RMBisim

theorem checked : allC {DATA}.test {DATA}.chunk{i:03} = true := by
  decide +kernel

end {NS}.{mod}
'''
def chunk_audit(i):
 mod=f'BisimRouting245Chunk{i:03}'
 return f'''import BusyBeaver.ZFC.{mod}
open {NS}
open RMBisim
#print axioms {mod}.checked

example : allC {DATA}.test {DATA}.chunk{i:03} = true := {mod}.checked
example {{j : Nat}} {{e : Entry}} (h : lookupC {DATA}.chunk{i:03} j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree {DATA}.cert e = true :=
  lookupC_all h {mod}.checked
'''

def final_source():
 imports=''.join(f'import BusyBeaver.ZFC.BisimRouting245Chunk{i:03}\n'for i in range(95))
 names=',\n    '.join(f'BisimRouting245Chunk{i:03}.checked'for i in range(95))
 return imports+f'''
/-! Complete source-program halting equivalence, conditional on no external
coverage premises: all95 exact blocks are assembled structurally below.
This is a source-program theorem, not a binary-machine or PA endpoint. -/
set_option autoImplicit false
namespace {NS}.BisimRouting245
open RegisterPath RMBisim

theorem all_ok : allC {DATA}.test {DATA}.cert = true := by
  rw [{DATA}.allC_decomposition]
  simp only [{names}, Bool.and_self]

theorem initial_programs :
    branchOk (ptree Prog254.program) (ptree ProgramRouting245.program)
      {DATA}.cert [] [] 0 = true := by
  rw [ActualTree254.tree_eq, TreeRouting245.tree_eq]
  exact {DATA}.initial_ok

theorem all_ok_programs :
    allC (entryOk (ptree Prog254.program) (ptree ProgramRouting245.program)
      {DATA}.cert) {DATA}.cert = true := by
  rw [ActualTree254.tree_eq, TreeRouting245.tree_eq]
  exact all_ok

/-- Same arbitrary register function, empty pointers, no execution/value bound. -/
theorem program_halts_iff (R : Registers) :
    Halts ProgramRouting245.program ⟨[], R⟩ ↔ Halts Prog254.program ⟨[], R⟩ :=
  (check_halts_iff initial_programs all_ok_programs R).symm

theorem program_nonhalting_iff (R : Registers) :
    ¬Halts ProgramRouting245.program ⟨[], R⟩ ↔ ¬Halts Prog254.program ⟨[], R⟩ :=
  not_congr (program_halts_iff R)

end {NS}.BisimRouting245
'''
def final_audit():
 return f'''import BusyBeaver.ZFC.BisimRouting245
open {NS}
open RegisterPath RMBisim
#print axioms BisimRouting245.all_ok
#print axioms BisimRouting245.initial_programs
#print axioms BisimRouting245.all_ok_programs
#print axioms BisimRouting245.program_halts_iff
#print axioms BisimRouting245.program_nonhalting_iff

example : allC {DATA}.test {DATA}.cert = true := BisimRouting245.all_ok
example : branchOk (ptree Prog254.program) (ptree ProgramRouting245.program)
    {DATA}.cert [] [] 0 = true := BisimRouting245.initial_programs
example : allC (entryOk (ptree Prog254.program) (ptree ProgramRouting245.program)
    {DATA}.cert) {DATA}.cert = true := BisimRouting245.all_ok_programs
example (R : Nat → Nat) : Halts ProgramRouting245.program ⟨[], R⟩ ↔
    Halts Prog254.program ⟨[], R⟩ := BisimRouting245.program_halts_iff R
example (R : Nat → Nat) : (¬Halts ProgramRouting245.program ⟨[], R⟩) ↔
    ¬Halts Prog254.program ⟨[], R⟩ := BisimRouting245.program_nonhalting_iff R
example (R : Nat → Nat) (h : Halts Prog254.program ⟨[], R⟩) :
    Halts ProgramRouting245.program ⟨[], R⟩ := (BisimRouting245.program_halts_iff R).mpr h
'''

def emit(stage,out,index):
 raw=validate_inputs();assert out.is_absolute() and str(out).startswith('/tmp/') and not out.exists()
 if stage=='data':mod=DATA;s,a=data_source(),data_audit();probes,callers=4,5
 elif stage=='chunk':
  assert index is not None and 0<=index<95;mod=f'BisimRouting245Chunk{index:03}';s,a=chunk_source(index),chunk_audit(index);probes,callers=1,2
 else:mod='BisimRouting245';s,a=final_source(),final_audit();probes,callers=5,6
 assert a.count('#print axioms ')==probes and a.count('\nexample ')==callers
 assert not re.search(r'\bsorry\b|\baxiom\s|native_decide|maxHeartbeats|maxRecDepth',s)
 if stage=='data':
  parsed={int(m[1]):m[2]for m in re.finditer(r'def chunk(\d{3}) : CTree := (.*)\n',s)}
  assert set(parsed)==set(range(95)) and all(parsed[i]==projection(paths[i])for i in range(95))
  assert re.search(r'def assembly : CTree :=\n  (.*)\n',s)[1]==cexpr(TREE)
  assert 'BisimRouting245Pilot.chunk' not in s and '.leaf (' not in s
 if stage=='final':
  assert re.findall(r'import BusyBeaver.ZFC.BisimRouting245Chunk(\d{3})',s)==[f'{i:03}'for i in range(95)]
  assert re.findall(r'BisimRouting245Chunk(\d{3})\.checked',s)==[f'{i:03}'for i in range(95)]
 out.mkdir(parents=True);(out/(mod+'.lean')).write_text(s);(out/'Audit.lean').write_text(a)
 record={'status':'SOURCE_ONLY_NOT_COMPILED','stage':stage,'module':'BusyBeaver.ZFC.'+mod,'source':desc(out/(mod+'.lean')),'audit':desc(out/'Audit.lean'),'generator':desc(Path(__file__)),'pilot_source':desc(PILOT),'plain_certificate':desc(CERT),'full_certificate_pairs':3013,'block_count':95,'block_index':index if stage=='chunk'else None,'block_range':blocks[index]if stage=='chunk'else None,'named_probes':probes,'typed_callers':callers,'source_direct_imports':re.findall(r'^import (.*)$',s,re.M),'private_pilot_identifier_references':False,'default_proof_limits':True,'full_certificate_for_successor_lookup':True,'compiler_execution':False,'guard_execution':False,'segment_execution':False,'structural_paths':paths if stage=='data'else None}
 (out/'source-inventory.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k]for k in ['stage','module','source','audit','named_probes','typed_callers']},indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['data','chunk','final'],required=True);ap.add_argument('--index',type=int);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();emit(args.stage,args.output.resolve(),args.index)
