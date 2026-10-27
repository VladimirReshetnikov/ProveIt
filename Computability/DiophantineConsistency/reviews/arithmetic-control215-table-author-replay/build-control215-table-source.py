from pathlib import Path
from functools import lru_cache
import re,json,hashlib
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
program=B/'KSource215Program.lean'
assert sha(program)=='7ab40d3faf9ddb976cdac2f77727e9e43b99b13a81fb45a340ad99abdfcd8310'
nodes={}
for line in program.read_text().splitlines():
 m=re.match(r'\s*\| (\d+) =>',line)
 if m:
  es=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',line)
  assert len(es)==2
  nodes[int(m[1])]=tuple((op,int(v)if v else 0)for op,v in es)
assert set(nodes)==set(range(179))
@lru_cache(None)
def size(e):return sum(size(x)for x in nodes[e[1]])if e[0]=='node'else 1
def leaves(e,p=()):
 if e[0]!='node':return [(p,e)]
 a,b=nodes[e[1]];return leaves(a,p+(False,))+leaves(b,p+(True,))
def inc(p):
 p=list(p);i=len(p)-1
 while i>=0 and p[i]:p[i]=False;i-=1
 if i>=0:p[i]=True
 return p
def strip(p,bit,n):
 i=len(p)
 while i>0 and n>0:
  i-=1
  if p[i]==bit:n-=1
 return p[:i]
def resolve(p):
 e=('node',178);i=off=0
 while e[0]=='node':
  a,b=nodes[e[1]];bit=p[i]if i<len(p)else False;i+=1
  if bit:off+=size(a);e=b
  else:e=a
 return off+1
phys=[6,2,0,4,3,7,8,5,1];rows=[]
for p,(op,r)in leaves(('node',178)):
 if op=='halt':row=(4,0,0,0)
 elif op=='inc':q=resolve(inc(p));row=(1,phys[r],q,q)
 elif op=='decnz':row=(2,phys[r],resolve(inc(strip(p,False,1))),resolve(inc(p)))
 elif op=='brk':q=resolve(inc(strip(p,False,r)));row=(3,0,q,q)
 elif op=='cont':q=resolve(strip(p,True,r));row=(3,0,q,q)
 else:raise AssertionError(op)
 rows.append(row)
assert len(rows)==4751
rowsha=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()
assert rowsha=='7bbbab9793f6e6ec2b82593b9ad51b8845753b1a1658ca40517adf30a12c938f'
packed=0
for i,(op,reg,q0,q1)in enumerate(rows):
 assert op<8 and reg<9 and q0<8192 and q1<8192
 packed|=(op+(reg<<3)+(q0<<7)+(q1<<20))<<(36*i)
assert packed<2**(36*4751)
decoded=[]
for i in range(4751):
 x=(packed>>(36*i))%2**36
 decoded.append((x%8,(x//8%16)%9,x//128%8192,x//1048576%8192))
assert decoded==rows
old=B/'ArithmeticDagControlPerm222.lean'
assert sha(old)=='1851444d564e63c2296c2e64335d95008465da9c1fd837bef399886f691e7fb4'
s=old.read_text();body=s[s.index('def count :'):s.index('/-- Every ordinary root exit')]
body=body.replace('packedRows','packed215')
for a,b in [('table_length','table215_length'),('table_eq_catalogue','table215_eq_catalogue'),('table','table215'),('rowsLit','rows215')]:
 body=re.sub(r'(?<!\.)\b'+a+r'\b',b,body)
body=body.replace('/-- Exactly the expression defining the existing pathDagPerm, without its\nlarge unrelated certificate-data import. -/\ndef path : RegisterPath.Program := RMEquiv.ofDag DagPerm.dagPerm 487',
 '/-- The actual existing program, not a copied node definition. -/\nabbrev path : RegisterPath.Program := KSource215.p215')
body=body.replace('RMBisim.ptree path','KSource215.t215')
head='''import BusyBeaver.ZFC.ArithmeticDagControlPerm222
import BusyBeaver.ZFC.KSource215Program

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! The complete packed control catalogue of the actual p215 program.
All 4,751 rows and the absence of higher packed bits are checked by the kernel.
The represented interpreter is internal to every model of IΣ1; no DagPerm
bisimulation, Turing-machine simulation, or HA endpoint is claimed here. -/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControl215Table

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisim (Row sem)
open ArithmeticControlFile (regValue liveValue)
open ArithmeticControlTable (write)

/-- All actual p215 rows in 36-bit slots, in false-first catalogue order. -/
def packed215 : Nat := 0x'''+format(packed,'x')+'\n\n'
tail='''/-- A concrete instruction from the actual table. -/
theorem first_row : rows215 1 = some ⟨2, 1, 3, 2⟩ := by decide +kernel

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev run215 (t x : V) : V := ArithmeticControlTable.controlRun table215 t x

theorem spec215 (c : Nat) (row : Row) (x : V) (h : rows215 c = some row) :
    ArithmeticControlTable.stepValue table215 (liveValue (c : V) x) =
      sem regValue write liveValue row x := by
  obtain ⟨hc, hg⟩ := PackedTables.rowsOf_some packed215 count c row h
  exact ArithmeticControlTable.spec_get table215 c row x hc hg

theorem run215_zero (x : V) : run215 0 x = x := ArithmeticControlTable.controlRun_zero table215 x

theorem run215_one (x : V) : run215 1 x = ArithmeticControlTable.stepValue table215 x :=
  ArithmeticControlTable.controlRun_one table215 x

theorem run215_add (t u x : V) : run215 (t + u) x = run215 u (run215 t x) :=
  ArithmeticControlTable.controlRun_add table215 t u x

theorem run215_halted (t : V) : run215 t 0 = 0 := ArithmeticControlTable.controlRun_halted table215 t

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControl215Table
'''
main=B/'ArithmeticControl215Table.lean';assert not main.exists();main.write_text(head+body+tail)
checks=B/'ArithmeticControl215TableChecks.lean';assert not checks.exists()
checks.write_text('''import BusyBeaver.ZFC.ArithmeticControl215Table

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControl215TableChecks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControl215Table
open ArithmeticControlFile (regValue liveValue)

example : path = KSource215.p215 := rfl
example : path.root = 178 := rfl
example : path.nnodes = 179 := rfl
example : table215.length = 4751 := table215_length
example : packed215 < 2 ^ (36 * count) := packed215_bound
example : table215 = (ControlCatalogue.leafEntries KSource215.t215).map
    (ArithmeticControlTable.rowOf KSource215.t215) := table215_eq_catalogue

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₂[V] run215 := inferInstance

theorem first_zero_step (x : V) (hz : regValue x 1 = 0) :
    run215 1 (liveValue 1 x) = liveValue 3 x := by
  rw [run215_one]
  simpa [ArithmeticControlBisim.sem, hz] using spec215 1 ⟨2, 1, 3, 2⟩ x first_row

example (t u x : V) : run215 (t + u) x = run215 u (run215 t x) := run215_add t u x
example (t : V) : run215 t 0 = 0 := run215_halted t
end Model

#print axioms packed215_bound
#print axioms table215_length
#print axioms table215_eq_catalogue
#print axioms spec215
#print axioms run215_zero
#print axioms run215_one
#print axioms run215_add
#print axioms run215_halted
#print axioms first_zero_step

end SetTheory.BusyBeaver.ZFC.ArithmeticControl215TableChecks
''')
audit={'scope':'Exact all-row source reconstruction and packed round trip; not a replacement for Lean catalogue equality.',
 'program':{'path':str(program),'sha256':sha(program)},'template':{'path':str(old),'sha256':sha(old)},
 'rows':len(rows),'row_sha256':rowsha,'physical_map':phys,'packed_bit_length':packed.bit_length(),
 'packed_hex_digits':len(format(packed,'x')),'packed_hex_sha256':hashlib.sha256(format(packed,'x').encode()).hexdigest(),
 'all_slots_roundtrip':True,'unused_high_bits_zero':True,
 'main':{'path':str(main),'sha256':sha(main)},'checks':{'path':str(checks),'sha256':sha(checks)},
 'generator':{'path':__file__,'sha256':sha(__file__)}}
Path('/tmp/control215-table-source-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(audit,indent=2))
