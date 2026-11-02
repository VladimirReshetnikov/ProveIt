#!/usr/bin/env python3
"""Source-only candidate closure; graph author overlay is provisional, not a trusted pair."""
import collections, hashlib, json, os, re, subprocess
from pathlib import Path
base=Path('Computability/DiophantineConsistency')
lean=base/'Lean/DiophantineConsistency'
research=base/'research/ordinary12-ipra-bridge'
graph=Path('/tmp/compact44-graph-support-join-01/lib/DiophantineConsistency')
historical=Path('/tmp/ipra-compact-inverse-contextual-pair-01/author/lib/DiophantineConsistency')
paths=subprocess.check_output(['git','ls-files','--',str(lean),str(research)],text=True).splitlines()
byname=collections.defaultdict(list)
for p in paths:
    if p.endswith('.lean'): byname[Path(p).stem].append(Path(p))
alias={'CompactMarkedReverse':research/'compact44-row-transport-prototype/CompactMarkedReverseDraft.lean', 'CompactCyclicBridge':research/'compact44-row-transport-prototype/CompactCyclicBridgeDraft.lean'}
seen=set(); order=[]; inherited={}; issues=[]; other_imports=set()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def visit(name):
    if name in seen:return
    seen.add(name)
    obj=graph/(name+'.olean')
    if obj.is_file():
        inherited[name]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':sha(obj)}; return
    if obj.is_symlink(): issues.append({'module':name,'type':'dangling_overlay_link','target':os.readlink(obj)})
    candidates=byname[name]
    if name in alias: candidates=[alias[name]] if str(alias[name]) in paths else []
    elif (lean/(name+'.lean')) in candidates: candidates=[lean/(name+'.lean')]
    if len(candidates)!=1:
        issues.append({'module':name,'type':'ambiguous_or_missing_source','candidates':[str(p) for p in candidates]});return
    p=candidates[0]; raw=p.read_text(); imports=re.findall(r'^import\s+([\w.]+)',raw,re.M)
    for imp in imports:
        if imp.startswith('DiophantineConsistency.'): visit(imp.split('.',1)[1])
        else: other_imports.add(imp)
    order.append({'module':name,'source':str(p),'sha256':sha(p),'imports':imports})
for n in ['CompactMarkedTransport','CompactInverseInventory','CompactForbidden','CompactNoExtra','CompactMarkedReverse','CompactCyclicBridge','CompactWordDefinability','CompactWordExistence','ArithmeticWangSoundness']:
    visit(n)
def state(p):
    return {'path':str(p),'exists':p.exists(),'lexists':os.path.lexists(p),'realpath':str(p.resolve()),'sha256':sha(p) if p.is_file() else None}
obj='ModelDifferenceRing.olean'
result={'purpose':'source-only candidate; no Lean, no pair, no transitive provider authentication', 'graph_author_overlay':str(graph), 'historical_author_overlay':str(historical), 'candidate_modules':len(order),'ordered_sources':order,'direct_inherited':inherited,'unresolved':issues,'other_direct_imports':sorted(other_imports),'model_difference_ring':{'graph':state(graph/obj),'historical':state(historical/obj)}}
print(json.dumps(result,indent=2,sort_keys=True))
