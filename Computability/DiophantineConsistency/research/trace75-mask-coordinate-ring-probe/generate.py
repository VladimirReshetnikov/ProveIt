#!/usr/bin/env python3
"""Construct a factored 74-row Lean ring check from the retained 75-row graph."""
import hashlib,json,pathlib
H=pathlib.Path(__file__).resolve().parent
P=H.parents[1]/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
d=json.loads(P.read_text()); rows=d['source']; assert len(rows)==75
assert ['C','-','qmF','alpha'] in rows and ['G1','*','bJ','qmF'] in rows and ['G','+','G1','alpha'] in rows
names=['J','F','C','i','T','w','s','n','eta','zeta']; ports=['beta','K0','MC','MF']
new=[]
for name,op,a,b in rows:
 if name=='C': continue
 if name=='4Am1': name='fourAm1'
 if a=='4Am1': a='fourAm1'
 if b=='4Am1': b='fourAm1'
 if name=='G1': a='q'
 if name=='G': op='-';b='C'
 new.append((name,op,a,b))
assert len(new)==74
lines=['import DiophantineConsistency.TenPositiveTrace75','',
'/-! 74-row coordinate identity; positive-domain inverse is conditional. -/',
'set_option autoImplicit false','set_option maxRecDepth 16384','noncomputable section',
'namespace Trace74Mask','open DiophantineConsistency.TenPositiveTrace75',
'variable {R : Type*} [CommRing R]','']

def make(name, core=False):
 args='(p : Fin 4 → R) (v : Fin 10 → R)'+(' (mask rankPart : R)' if core else '')+' : R :='
 result=['def '+name+' '+args]
 result += ['  let '+n+' : R := v '+str(i) for i,n in enumerate(names) if not (core and n=='C')]
 if core: result += ['  let C : R := mask']
 result += ['  let '+n+' : R := p '+str(i) for i,n in enumerate(ports)]
 for n,op,a,b in new:
  if core and n in ('qmF','G1'): continue
  if core and n=='G': result += ['  let G : R := rankPart'];continue
  result += [f'  let {n} := {a} {op} {b}']
 return result+['  N','']
lines += make('value74')+make('core',True)
lines += ['def oldVal (p : Fin 4 → R) (v : Fin 10 → R) : Fin 10 → R :=',
'  fun i => if i = 2 then (p 0 * v 0 + 1) - v 1 - v 2 else v i','',
'theorem coordinate_identity (p : Fin 4 → R) (v : Fin 10 → R) :',
'    value74 p v = value75 p (oldVal p v) := by',
'  change core p v (v 2) ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) - v 1) - v 2) =',
'    core p v ((p 0 * v 0 + 1) - v 1 - ((p 0 * v 0 + 1) - v 1 - v 2))',
'      (p 0 * v 0 * ((p 0 * v 0 + 1) - v 1) + ((p 0 * v 0 + 1) - v 1 - v 2))',
'  congr 1 <;> ring','','#print axioms coordinate_identity','end Trace74Mask','']
(H/'Trace74Mask.lean').write_text('\n'.join(lines))
print('parent_sha256',hashlib.sha256(P.read_bytes()).hexdigest());print('lean_sha256',hashlib.sha256((H/'Trace74Mask.lean').read_bytes()).hexdigest())
