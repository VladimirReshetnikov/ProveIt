#!/usr/bin/env python3
"""Source/replay and arithmetic checks only; deliberately does not claim Lean checking."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile
OUT=Path(__file__).resolve().parent
ROOT=OUT.parent
REL=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPowerCoordinates2011.lean')
old=(ROOT/'sources'/REL).read_text()
new=(OUT/'CurrentPowerCoordinates2011.lean').read_text()
meta=json.loads((OUT/'metadata.json').read_text())
def require(test,message):
    if not test:
        raise AssertionError(message)
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
require(sha(old)==meta['old_sha256'],'source sha256 changed')
require(sha(new)==meta['new_sha256'],'candidate sha256 changed')
require(len(old.splitlines())==105 and len(new.splitlines())==102,'complete-file counts changed')
headers=lambda s:re.findall(r'(?ms)^(?:private )?theorem .*? :=',s)
require(headers(old)==headers(new),'public theorem header changed')
require(re.findall(r'(?m)^import .*$',old)==re.findall(r'(?m)^import .*$',new),'imports changed')
require(new.index('theorem full_order')<new.index('theorem generator_cast_C0'),'full_order not before client')
require('generator_cast_auxiliary' not in new[new.index('theorem full_order'):new.index('theorem generator_cast_C0')],'cyclic proof dependency')
aux=(ROOT/'sources'/REL.with_name('CurrentAuxiliaryOrder2011.lean')).read_text()
require('import DiophantineConsistency.CurrentPowerCoordinates2011' not in aux,'new import cycle')
require('theorem generator_order_succ' in aux,'imported source theorem absent')
p=120199;d=47*2011;e=94517*(p-1)
checks={str(m):pow(2,e,m) for m in [47,2011,p,d*p,p*p]}
require(all(checks[str(m)]==1 for m in [47,2011,p,d*p]),'zero-index generator test failed')
require(checks[str(p*p)]==7300767062!=1,'nontrivial first lift changed')
with tempfile.TemporaryDirectory(dir='/tmp') as td:
    target=Path(td)/REL;target.parent.mkdir(parents=True);target.write_text(old)
    r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(OUT/'order_zero_specializations.patch')],cwd=td,capture_output=True,text=True)
    require(r.returncode==0,r.stdout+r.stderr)
    require(target.read_text()==new,'patch output differs from complete replacement')
print(json.dumps({'source_replay_pass':True,'old_lines':105,'new_lines':102,'modular_power_crosschecks':checks,'lean_checked':False},indent=2))
