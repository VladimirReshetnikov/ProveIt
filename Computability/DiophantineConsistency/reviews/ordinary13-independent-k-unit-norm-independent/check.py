from pathlib import Path
from hashlib import sha256
import json,itertools,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-unit-norm-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-independent-k-unit-norm-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());s=(P/'IndependentKUnitGraph.lean.src').read_text()
slots=re.findall(r'^  let (n_\w+) : Expr \(Fin 13\) := .var (\d+)$',s,re.M)
assert slots==[(n,str(i)) for i,n in enumerate(g['witnesses'])]
ports=re.findall(r'^  let (\w+) : Expr \(Fin 13\) := .constant \(p (\d+)\)$',s,re.M)
assert ports==[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])]
rows=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',s,re.M)
assert len(rows)==84
def atom(x):return int(x) if x.isdigit() else x
assert [[n,op,atom(x),atom(y)] for n,x,op,y in rows]==g['source']
fields=['first','main','aux','strong','output','strongResidual','b','z','x','s','k','u','a','c','d','y','vv','f','ii','ell','delta']
assert re.findall(r'^  (\w+) : Expr \(Fin 13\)$',s,re.M)==fields
assert re.search(r'⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, n_k, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩',s)
assert 'kbase' not in s and 'n_zeta' not in s
bridge=(P/'IndependentKUnitBridge.lean.src').read_text()
parent=Path('research/ordinary13-eta-zeta-natural-unit-norm-draft/EtaZetaNaturalUnitBridge.lean.src').read_text()
parent=parent.replace('import EtaZetaNaturalUnitGraph','import IndependentKUnitGraph').replace('EtaZetaNaturalUnitBridgeDraft','IndependentKUnitBridgeDraft').replace('EtaZetaNaturalUnitGraphDraft','IndependentKUnitGraphDraft').replace('exact eta/zeta-natural\nprototype','exact independent-k\nchild candidate')
assert bridge==parent
assert '(hz : InternalZero (graph p).output v)' in bridge
assert 'let k := (graph p).k.evalRing e' in bridge
assert 'theorem first_pattern' in bridge and 'theorem signed_norms' in bridge
free=Path('Lean/DiophantineConsistency/Compact44/FreeJ13.lean').read_text()
for a in ('def mainPattern','def auxPattern','def strongPattern','theorem main_ne','theorem aux_ne','theorem strong_ne','theorem unit_iff_one'):assert a in free
pairs=Path('Lean/DiophantineConsistency/ArithmeticSignedPairs.lean').read_text()
units=Path('Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean').read_text()
for x in ('theorem product5_magnitudes','theorem positive_of_magnitude_one','theorem equivalent_one'):
 assert x in pairs
for x in ('theorem pairEval_residue','theorem negative_residue'):
 assert x in units
# Finite universals independently verify all four residue patterns.
for b,z,x,s0,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s0;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4 != 3
for u,a,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(3+4*a+a*a)*c*c))%4 != 3
for y,z,a,f in itertools.product(range(4),repeat=4):
 delta=3+4*a+a*a;Q=delta*(f*f-1)
 assert (y*y-Q*(y*y-z*z))%4 != 3
for i,a,f in itertools.product(range(4),repeat=3):
 assert (1+i*i-(3+4*a+a*a)*(f*f-1))%4 != 3
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'candidate_rows_independently_parsed':len(rows),'all_13_slots_and_four_port_indices':True,
 'structure_field_to_row_mapping_exact':True,'parent_bridge_adaptation_exact':True,
 'author_receipt_reproduced':True,'four_generic_mod_four_patterns_exhausted':True,
 'lean_executed':False,'source_elaboration_or_provider_validation':False},indent=2,sort_keys=True))
