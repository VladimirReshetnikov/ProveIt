#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent; candidate=h.parent/'trace73-center-probe/candidate.json'; raw=candidate.read_bytes()
if sha256(raw).hexdigest()!='c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6': raise SystemExit('candidate hash mismatch')
c=json.loads(raw); names={n:f'(v {i})' for i,n in enumerate(c['witnesses'])}; names.update({n:f'(p {i})' for i,n in enumerate(c['fixed_numerals'])})
lines=['import Trace73CenterV2','','set_option autoImplicit false','set_option Elab.async false','set_option maxRecDepth 16384','noncomputable section','namespace Trace73Literal','variable {R : Type*} [CommRing R]','','def graph73 (p : Fin 4 → R) (v : Fin 10 → R) : R :=']
for i,(n,op,a,b) in enumerate(c['source'],1):
 def arg(x): return str(x) if type(x)==int else names[x]
 lines.append(f'  let g{i:02} := {arg(a)} {op} {arg(b)}'); names[n]=f'g{i:02}'
lines.extend([f'  {names[c["output"]]}','','theorem literal_eq (p : Fin 4 → R) (v : Fin 10 → R) :','    graph73 p v = Trace73Center.value73 p v := by','  rfl','','theorem parent_substitution (p : Fin 4 → R) (v : Fin 10 → R) :','    DiophantineConsistency.TenPositiveTrace75.value75 p (Trace73Center.lift p v) = graph73 p v := by','  rw [Trace73Center.substitution, literal_eq]','','#print axioms Trace73Literal.literal_eq','#print axioms Trace73Literal.parent_substitution','end Trace73Literal',''])
out=h/'Trace73Literal.lean'
if out.exists() or out.is_symlink(): raise SystemExit('output already exists')
out.write_text('\n'.join(lines)); print(sha256(out.read_bytes()).hexdigest())
