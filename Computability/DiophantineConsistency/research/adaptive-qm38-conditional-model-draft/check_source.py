#!/usr/bin/env python3
"""Exact source/coordinate checks and finite controls; no Lean proof."""
from pathlib import Path
import ast,hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
child=json.loads(pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'))
parent=json.loads(pin(D/'research/adaptive-square-sums40-quotient-quartic/candidate.json','fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d'))
old=pin(D/'Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece')
native=pin(D/'Lean/DiophantineConsistency/IPRAQM40Native.lean','d261c83bf10cd406063b6622b477dac4aefe0a811f1e471ad5142e587864d40b')
zeros=pin(D/'Lean/DiophantineConsistency/AdaptiveQM40Zeros.lean','b90faa5bace82f3352b94c5d5fade8cc3477cab3017de5ac9dc35dc8a73ce482')
literal=pin(P/'AdaptiveQM38Literal.lean.src','f033af128e5ca4c7a5a1473e6370fc385d0354b110067ae84e168eed6643a44d')
transfer=pin(P/'AdaptiveQM38ConditionalTransfer.lean.src','104e56bcbc2ef2c922864c443b607fdc69ea048a8546d7c1d69340c6e7c7b588')
slots=pin(P/'AdaptiveQM38ParentSlots.lean.src','9fa0f09927c327a6debf46dd894db4ce7f0ef746f07fd908aeb24b26cd3e5c42')
cut=pin(P/'AdaptiveQM38EvaluationCut.lean.src','08707aa597d45389ab038fcda534d342ec4487913da52832ea441241fa9fee0b')
pin(P/'generate_literal.py','995f6eb7e94942d4556cdf6bd4c1574bff76b2316c156c6583db28695a1dfa29')
# Check both literal source schedules, not numerical samples alone.
start=old.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n');end=old.index('\ntheorem literal_eq ',start)
exp=['def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=']+[f'  let {n} : Expr (Fin 40) := .var {i}' for i,n in enumerate(parent['witnesses'])]+[f'  let {n} : Expr (Fin 40) := .constant (p {i})' for i,n in enumerate(parent['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in parent['source']]+['  '+parent['output']]
assert old[start:end].splitlines()==exp
for i,n in enumerate(child['witnesses']):assert f'let {n} : Expr (Fin 38) := .var {i}' in literal
for i,n in enumerate(child['fixed_numerals']):assert f'let {n} : Expr (Fin 38) := .constant (p {i})' in literal
section=literal.split('-- BEGIN GENERATED ROWS\n',1)[1].split('\n  -- END GENERATED ROWS',1)[0]
program=ast.parse('\n'.join(line.strip()[4:].replace(':=','=') for line in section.splitlines()))
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
def arg(x):
 if isinstance(x,ast.Name):return x.id
 assert isinstance(x,ast.Constant) and type(x.value)==int;return x.value
rows=[]
for x in program.body:
 assert isinstance(x,ast.Assign) and len(x.targets)==1 and isinstance(x.targets[0],ast.Name) and isinstance(x.value,ast.BinOp) and type(x.value.op) in ops
 rows.append([x.targets[0].id,ops[type(x.value.op)],arg(x.value.left),arg(x.value.right)])
assert rows==child['source'] and len(rows)==160 and child['output']=='add_timeProduct'
assert child['witnesses']==[x for x in parent['witnesses'] if x not in {'ellProductVariable','deltaProductVariable'}]
assert parent['witnesses'][29]=='ellProductVariable' and parent['witnesses'][33]=='deltaProductVariable'
removed={'ellProductDifference','ellProductConstraint','add_ellProduct','deltaProductDifference','deltaProductConstraint','add_deltaProduct'}
changes={'g41':['g41','+',1,'g40'],'g64':['g64','+',1,'g63'],'add_scaledIndex':['add_scaledIndex','+','add_product2','scaledIndexConstraint'],'add_rankSeed':['add_rankSeed','+','add_qSigned','rankSeedConstraint']}
assert child['source']==[changes.get(r[0],r) for r in parent['source'] if r[0] not in removed]
# The parent residual indices referenced by the proposed Lean source.
start=old.index('def residuals (p : Fin 4 → ℤ) : Fin 31 → Expr (Fin 40) :=');end=old.index('\ndef literal (p : Fin 4 → ℤ)',start)
residuals=re.findall(r'  !\[([^\n]+)\]',old[start:end]);assert len(residuals)==1
rr=residuals[0].split(',');assert len(rr)==31 and rr[20]=='ellProductDifference' and rr[24]=='deltaProductDifference'
assert 'theorem new_all' in zeros and '∀ i : Fin 31' in zeros
assert '(AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)' in native and 'theorem bridge40' in native
for term in ('(hproject :','(hextend :','ZeroPreservationObligations','theorem native_equivalence (h : ZeroPreservationObligations)'):
 assert term in transfer
assert '(hcut : EvaluationCut)' in cut and 'slot29_of_zero' in cut and 'slot33_of_zero' in cut
assert 'mp hz 20' in slots and 'mp hz 24' in slots
# Check the actual coordinate formulas and forward output identity on finite
# controls. These controls are not universal model proofs.
rng=random.Random(3816079);mod=1000000007
for _ in range(100):
 v=[rng.randrange(1,12) for _ in range(38)];ports=[rng.randrange(-5,6) for _ in range(4)]
 ext=[]
 for i in range(40):
  if i==29:ext.append(v[17]*(v[17]+(v[9]+v[10])))
  elif i==33:ext.append(v[26]*v[22])
  elif i<29:ext.append(v[i])
  elif i<33:ext.append(v[i-1])
  else:ext.append(v[i-2])
 proj=[ext[i if i<29 else i+1 if i<32 else i+2] for i in range(38)];assert proj==v
 assert all(x>0 for x in ext)
 def ev(g,vs):
  e=dict(zip(g['witnesses'],vs));e.update(zip(g['fixed_numerals'],ports))
  for n,o,a,b in g['source']:
   a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
   e[n]=(a+b if o=='+' else a-b if o=='-' else a*b)%mod
  return e[g['output']]
 assert ev(parent,ext)==ev(child,v)
print(json.dumps({'scope':'exact source/coordinate transcription and finite forward controls only; no Lean, universal evaluation cut or proof','parent_rows':len(parent['source']),'child_rows':len(child['source']),'child_variables':len(child['witnesses']),'deleted_parent_slots':[29,33],'parent_residual_indices':[20,24],'finite_modular_forward_controls':100,'zero_maps_explicit_hypotheses':True,'evaluation_cut_unproved':True},sort_keys=True,indent=2))
