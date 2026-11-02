#!/usr/bin/env python3
"""Point-in-time independent review; does not launch Lean or rebuild parents."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('requires nonoptimized python3 -I -S')
BASE = Path(__file__).resolve().parents[2]
PLAN = BASE / 'research/ordinary12-ipra-bridge/free-j-first-congruence-closure-plan'
SOURCE = BASE / 'research/ordinary12-ipra-bridge/free-j-first-congruence-prototype/FreeJGraphCongruenceExplore.lean'
PARENT = BASE / 'reviews/compact44-graph-derived-radix-independent-audit'
LIBS = [Path('/tmp/ipra-compact-graph-derived-radix-pair-01') / s / 'lib' for s in ('author', 'peer')]
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS = {PLAN/'scan.py':'48a0e4db97fc1b706189ffc2236b7189f83cbcd401ac3c1d25aef9a0ddf6b9ab',
 PLAN/'scan.json':'e5189543fb90c67e7e9c16a3c80027f4ef962056f73318923230179f05596f87',
 PLAN/'README.md':'35532cd02a28b898ca072444746b3561838e020726fd78730615547188815d8e',
 SOURCE:'ae61e987e28267e6579c21843d989d0a960d782aa5905bc97b78d9ce28c98537',
 PARENT/'CHECK.json':'2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc',
 PARENT/'terminal-observation.json':'111f0b17cc873126d6c55fa40387c763ccfe5a7f616e03bd87d13fe3359e4c5b'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c, msg):
    if not c: raise ValueError(msg)
for p,h in PINS.items(): need(digest(p)==h, str(p))
data = json.loads((PLAN/'scan.json').read_bytes())
imports = [line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')]
need(imports == ['DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.ArithmeticModularCancellation'] == data['imports'], 'imports')
need(data['status']=='PRELIMINARY_CONGRUENCE_SOURCE_CLOSURE_NOT_A_BUILD', 'scope')
parent = json.loads((PARENT/'CHECK.json').read_bytes())
obs = json.loads((PARENT/'terminal-observation.json').read_bytes())
need(parent['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==PINS[PARENT/'CHECK.json'], 'parent receipt')
objects = []
for lib in LIBS:
    objects.append({p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()})
need(set(objects[0])==set(objects[1]) and len(objects[0])==143, 'inventory paths')
for row in data['objects']:
    rel=row['path']; need(rel in objects[0] and digest(objects[0][rel])==row['sha256']==digest(objects[1][rel]), 'object '+rel)
    need(str(objects[0][rel].resolve())==row['author_resolved'] and str(objects[1][rel].resolve())==row['peer_resolved'], 'resolved '+rel)
need(len(data['objects'])==143 and len({r['path'] for r in data['objects']})==143, 'object rows')
slots=data['direct_project_companion_slots']; need(len(slots)==40,'slot count')
for lib in LIBS:
    for module in imports:
        stem=lib/Path(*module.split('.'))
        for suffix in SUFFIXES:
            p=Path(str(stem)+suffix); got=slots[str(p)]
            if got is None: need(not os.path.lexists(p), 'unexpected direct companion '+str(p))
            else: need(p.is_file() and digest(p)==got['sha256'] and str(p.resolve())==got['realpath'], 'direct companion '+str(p))
        need(Path(str(stem)+'.olean').is_file(), 'missing direct object')
    target=lib/'DiophantineConsistency/FreeJGraphCongruenceExplore'
    for suffix in SUFFIXES: need(not os.path.lexists(Path(str(target)+suffix)), 'output collision')
init=data['package_init']; p=Path(init['path'])
need(p.is_file() and digest(p)==init['sha256'] and str(p.resolve())==init['resolved_path'], 'Init')
run=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=120)
need(run.returncode==0 and not run.stderr and run.stdout==(PLAN/'scan.json').read_bytes(), 'author scan replay')
print(json.dumps({'status':'PASS_INDEPENDENT_FIRST_CONGRUENCE_SOURCE_CLOSURE','source_sha256':PINS[SOURCE],'scan_sha256':PINS[PLAN/'scan.json'],'parent_audit_sha256':PINS[PARENT/'CHECK.json'],'paired_object_count':143,'direct_companion_slots':40,'target_slots_checked':20,'lean_launched':False,'scope':'Point-in-time source/provider review; parent receipt checked but parent audit not rerun, no build or continuous input protection, no retained K binding, graph decoder or iPRA claim.'},indent=2,sort_keys=True))
