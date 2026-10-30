from pathlib import Path
import glob,json,hashlib
root=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');d=root/'reviews/adaptive-construction-driver-scope-correction-evidence';d.mkdir(parents=True,exist_ok=True)
scopes={
'AuxExact':'exact auxiliary orientation from the seed linear identity and auxiliary norm',
'AuxFactor':'literal auxiliary factor unit from explicit strong and auxiliary norms',
'AuxWitness':'positive auxiliary coordinate and literal factor unit for the explicit witness',
'Correction':'additive main-correction quotient from explicit Pell seed identities',
'CorrectionPositive':'positive main correction under explicit first-index hypotheses',
'CorrectionSeed':'positive main correction from the outer-seed relation',
'FactorLemmas':'reverse square-factor and strong-factor unit lemmas',
'FactorZero':'literal unshifted zero from four factor units and positive-shifted zero',
'FirstActual':'positive first carrier from actual old vector, seed and explicit radix/rank facts',
'FirstFactor':'literal first factor unit from additive first carrier and first norm',
'FirstPositive':'positive first carrier from first norm and explicit size assumptions',
'FirstSeed':'positive first carrier from the outer seed and explicit transport bound',
'FirstWitness':'attempted first literal factor unit for the concrete witness; see recorded status',
'MainExact':'exact main shift and scaled norm from additive correction data',
'MainFactor':'literal main factor unit from additive shift and main norm',
'MainSeed':'positive main coordinate and scaled norm from outer seed',
'MainWitness':'positive main coordinate and literal factor unit for the concrete witness',
'SeedSize':'first-seed ordinate size from explicit index and ordinate identities',
'TransportActual':'nonzero transport quotient from actual old equations and explicit radix/rank facts',
'TransportPositive':'multiplier and transport-quotient positivity from explicit conditions',
'Witness':'explicit thirteen-coordinate witness and its strong factor unit',
'WitnessPositive':'positivity of the explicit witness from positive input coordinates'}
label='model-uniform main-correction quotient from explicit Pell seed identities; no positivity or actual assembly claim';paths=glob.glob('/tmp/adaptive-construction-*/state.json')+glob.glob(str(root/'reviews/adaptive-construction*/*/state.json'));groups={}
for p in sorted(paths):
 try:
  raw=Path(p).read_bytes();s=json.loads(raw)
 except (OSError,ValueError):continue
 if s.get('scope')!=label:continue
 names=[x for x in s.get('snapshots',{}) if not x.endswith('Checks')]
 if not names:raise RuntimeError('missing snapshots: '+p)
 target=names[-1];prefix='ArithmeticAdaptiveConstruction';suffix='2011'
 if not target.startswith(prefix) or not target.endswith(suffix):raise RuntimeError('unknown target '+target)
 key=target[len(prefix):-len(suffix)]
 if key not in scopes:raise RuntimeError('unknown scope '+key)
 if key=='Correction':continue
 digest=hashlib.sha256(raw).hexdigest();row=groups.setdefault(digest,{'sha256':digest,'original_paths':[],'private':s.get('private'),'status':s.get('status'),'primary_module':target,'snapshot_modules':names,'correct_scope':scopes[key],'recorded_scope':label,'retained_state':'states/'+digest+'.json'});row['original_paths'].append(p);out=d/'states'/f'{digest}.json';out.parent.mkdir(exist_ok=True);out.write_bytes(raw)
rows=sorted(groups.values(),key=lambda a:(a['primary_module'],a['private'] or ''));(d/'states.json').write_text(json.dumps(rows,indent=2)+'\n');manifest=[]
for p in sorted(d.rglob('*')):
 if p.is_file() and p.name!='FILES.json':
  raw=p.read_bytes();manifest.append({'path':str(p.relative_to(d)),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
(d/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n');print('states',len(rows),'paths',sum(len(x['original_paths']) for x in rows),'manifest',hashlib.sha256((d/'FILES.json').read_bytes()).hexdigest())
