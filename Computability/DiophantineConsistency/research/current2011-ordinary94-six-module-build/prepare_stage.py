#!/usr/bin/env python3
"""Prepare exactly one independently guarded source stage; does not run Lean."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
OVER=Path('/tmp/current2011-ordinary94-six-overlay-20261105/lib')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SURVEY=HERE/'survey-result-snapshot.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
need(len(sys.argv)==2 and sys.argv[1] in ('1','2','3','4','5'),'stage 1..5 required')
n=int(sys.argv[1]);need(sha(SURVEY)=='d923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821','survey drift')
d=json.loads(SURVEY.read_text());name=d['minimal_extra_order'][n];entry=d['minimal_extra_sources'][name]
source=TASK/'Lean'/Path(*name.split('.')).with_suffix('.lean');need(sha(source)==entry['source_sha256'],'source drift')
refs={}
for mod in entry['imports']:
    stem=Path(*mod.split('.'));hits=[r/(str(stem)+'.olean') for r in (OVER,PKG) if (r/(str(stem)+'.olean')).is_file()]
    need(len(hits)==1,'missing or ambiguous direct module '+mod+': '+repr(hits))
    refs[str(stem)]=(str(hits[0]),sha(hits[0]))
need(not (OVER/(name.replace('.','/')+'.olean')).exists(),'output present')
base=(TASK/'research/current2011-ordinary67-94-syntax-fresh/check01.py').read_text()
a=base.index('DIRECT = {');b=base.index('\nOUT =',a)
base=base[:a]+'DIRECT = '+repr(refs)+base[b:]
base=base.replace("SOURCE = HERE.parents[1]/'Lean/DiophantineConsistency/Carrier94Syntax.lean'",'SOURCE = Path('+repr(str(source))+')')
base=base.replace('/tmp/current2011-ordinary67-94-syntax-fresh-check01',f'/tmp/current2011-ordinary94-stage{n:02d}-check01')
base=base.replace("obj = OUT/'Carrier94Syntax.olean'", "obj = OUT/"+repr(name.split('.')[-1]+'.olean'))
base=base.replace("LEAN_PATH = '/tmp/normalized106-fresh-model-build-v2-20261105/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'",'LEAN_PATH = '+repr(str(OVER)+':'+str(PKG)))
old="'/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier94Syntax.lean': 'b68f54257ff1ebab090ed45e83d6c3719be51ccb0f7a7f03822e333bbb43ea8d'"
base=base.replace(old,repr(str(source))+': '+repr(entry['source_sha256']))
base=base.replace(' str(LEAN):',repr(str(SURVEY))+": 'd923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821',\n '/tmp/current2011-ordinary94-six-overlay-20261105/overlay.json': '607e33f8290b8c4338e844b59334b0ad7b635c7e7b699c40a74e3274c4714e1e',\n str(LEAN):")
base=base.replace('Fresh-base compile of literal Carrier94Syntax module, no endpoint theorem',f'Fresh-base stage {n} {name}; direct input guards only, no endpoint theorem')
p=HERE/f'stage{n:02d}.py';need(not p.exists(),'runner exists');p.write_text(base)
print(json.dumps({'stage':n,'module':name,'source_sha256':sha(source),'runner':str(p),'runner_sha256':sha(p),'direct':refs},sort_keys=True))
