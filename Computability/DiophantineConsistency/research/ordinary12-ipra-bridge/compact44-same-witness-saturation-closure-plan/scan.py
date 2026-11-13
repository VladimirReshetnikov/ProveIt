#!/usr/bin/env python3
"""Point-in-time three-source graph-radix provider survey; no Lean build."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('requires nonoptimized python3 -I -S')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT/'Computability/DiophantineConsistency'
RESEARCH = BASE/'research/ordinary12-ipra-bridge'
AUDIT = BASE/'reviews/compact44-graph-derived-radix-independent-audit'
PARENT = Path('/tmp/ipra-compact-graph-derived-radix-pair-01')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
ROWS = [
 ('FreeJGraphCongruenceExplore','free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean','f3afbc380f','d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0',['CompactGraphDerivedRadix','ArithmeticModularCancellation']),
 ('CompactSymbolicGraphSaturation','compact44-symbolic-saturation-prototype/CompactSymbolicGraphSaturation.lean','0ba22c687e','812a757a038d63873ad94a02c310c79800f1ed98abd18b6fe1cd17445b556e8a',['FreeJConcreteDigitsClient','CompactLowExact','CompactLowEven','CompactHighResidue']),
 ('CompactSameWitnessSaturation2','compact44-same-witness-saturation-prototype/CompactSameWitnessSaturation2.lean','b3c898e2c4','246e900e939b0c6b6cbdc15f49eccc6bd07361c9816d099004ad59c79edb6afd',['FreeJGraphCongruenceExplore','CompactSymbolicGraphSaturation'])]
PARENT_HASH='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc'
OBS_HASH='111f0b17cc873126d6c55fa40387c763ccfe5a7f616e03bd87d13fe3359e4c5b'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,what):
    if not ok: raise ValueError(what)
def slots(stem):
    result={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            need(p.is_file(), 'invalid companion '+str(p))
            result[str(p)]={'sha256':digest(p),'realpath':str(p.resolve())}
        else: result[str(p)]=None
    return result
need(digest(AUDIT/'CHECK.json')==PARENT_HASH and digest(AUDIT/'terminal-observation.json')==OBS_HASH,'parent receipt pins')
check=json.loads((AUDIT/'CHECK.json').read_bytes()); obs=json.loads((AUDIT/'terminal-observation.json').read_bytes())
need(check['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==PARENT_HASH,'parent receipt')
sources=[]
for module,rel,commit,expected,imports in ROWS:
    source=RESEARCH/rel
    need(digest(source)==expected,'source '+module)
    blob=subprocess.run(['git','show',commit+':'+source.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
    need(hashlib.sha256(blob).hexdigest()==expected,'source commit '+module)
    actual=[line[7:] for line in source.read_text().splitlines() if line.startswith('import ')]
    need(actual==['DiophantineConsistency.'+name for name in imports],'imports '+module)
    sources.append({'module':'DiophantineConsistency.'+module,'source':str(source),'source_commit':commit,'source_sha256':expected,'imports':actual})
libs=[PARENT/side/'lib' for side in ('author','peer')]
inventory=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs]
need(set(inventory[0])==set(inventory[1]) and len(inventory[0])==143,'paired inventory paths')
objects=[]
for rel in sorted(inventory[0]):
    a,b=inventory[0][rel],inventory[1][rel]; need(digest(a)==digest(b),'paired object '+rel)
    objects.append({'path':rel,'sha256':digest(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
external=ROWS[0][4]+ROWS[1][4]
direct={}; targets={}
for lib in libs:
    for module in external:
        stem=lib/'DiophantineConsistency'/module
        need(Path(str(stem)+'.olean').is_file(),'missing direct '+str(stem))
        direct.update(slots(stem))
    for module,_,_,_,_ in ROWS:
        stem=lib/'DiophantineConsistency'/module
        snapshot=slots(stem); need(all(v is None for v in snapshot.values()),'target collision '+str(stem))
        targets.update(snapshot)
init=PACKAGE/'Init.olean'; need(init.is_file(),'missing Init')
init_slots=slots(PACKAGE/'Init')
for module,rel,_,expected,_ in ROWS: need(digest(RESEARCH/rel)==expected,'source drift '+module)
print(json.dumps({'status':'PRELIMINARY_SAME_WITNESS_SATURATION_CLOSURE_NOT_A_BUILD','source_order':sources,'parent_audit_sha256':PARENT_HASH,'objects':objects,'external_direct_companion_slots':direct,'target_companion_slots':targets,'package_init_companion_slots':init_slots,'scope':'Point-in-time three-source plan on paired graph-radix provider; no parent rerun or build, no complete package/transitive/dynamic ancestry, retained-port binding, decoder or internal iPRA proof.'},indent=2,sort_keys=True))
