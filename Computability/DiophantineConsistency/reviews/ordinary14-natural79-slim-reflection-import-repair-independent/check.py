#!/usr/bin/env python3
"""Independent lexical/source review; no Lean, no staging, no writes."""
from collections import deque
from pathlib import Path
import hashlib, json, re, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]; repo=D.parents[1]
R=D/'research'; p=R/'ordinary14-natural79-slim-reflection-import-repair'; draft=R/'ordinary14-natural79-dvd-reflection-slim-draft'
oldreview=D/'reviews/ordinary14-natural79-dvd-reflection-slim-independent'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes(); assert sha(b)==h,(str(p),sha(b)); return b
fixed=pin(p/'NaturalDvdReflectionSlim.lean.src','90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4')
orig=pin(draft/'NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb')
pin(p/'check_source.py','3396d3b121e2f39c74ee1cedf0eca17e18996e20f470a6d59085ae32ee636907')
report=json.loads(pin(p/'result.json','b441f7d6642584ea2f20bb2643179002dd02b8295252db31516b7ceb70832719'))
pin(oldreview/'check.py','40edae56a45cdd617150e9fa120943b8afaa258c360f7df80c9b8eff25d583e6')
old=json.loads(pin(oldreview/'result.json','2bb017e409f8b1e230cd298003b256b15aeaf180fa472333ad1be848ad2cf8da'))
assert fixed==b'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'+orig
assert old['projected_missing_sources']==5 and old['projected_frontier_objects']==41 and old['projected_external_objects']==5
precedent=pin(D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean','ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d').decode()
assert 'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n' in precedent
assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in precedent
base=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic')
basic=pin(base/'IOpen/Basic.lean','4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b').decode()
schemata=pin(base/'Schemata.lean','5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd').decode()
assert 'public import Foundation.FirstOrder.Arithmetic.Schemata' in basic
assert 'notation "𝗜𝚺₁" => ISigma 1' in schemata
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
obj=pkg/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean'
pin(obj,'fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45')
# Reconstruct the bounded project-source closure from pinned live files, using
# a lexical import scan. This does not compute Lean's resolved import graph.
rx=re.compile(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)',re.M)
roots=[D/'Lean',repo/'Computability/BusyBeaver/Lean']; q=deque(['DiophantineConsistency.ModelDifferenceRing']); seen=set(); sources={}; leaves=set()
while q:
 name=q.popleft()
 if name in seen: continue
 seen.add(name)
 if not name.startswith(('DiophantineConsistency.','BusyBeaver.')): leaves.add(name); continue
 rel=Path(*name.split('.')).with_suffix('.lean'); paths=[r/rel for r in roots if (r/rel).is_file()]; assert len(paths)==1,(name,paths)
 raw=paths[0].read_bytes(); sources[str(paths[0].relative_to(repo))]=sha(raw)
 for m in rx.finditer(raw.decode()):q.extend(m.group(1).split())
assert len(sources)==19 and sources==report['model_difference_ring_project_closure_source_sha256']
assert sorted(leaves)==report['model_difference_ring_nonproject_import_leaves'] and all(n.startswith('Mathlib.') for n in leaves)
# Check original projected external set and add the one newly explicit leaf.
cut=json.loads(pin(draft/'result.json','6ee95a0db3f72c4b49199e301f1f63812e9723b0e55ac8af3662e87722599ea6')); ext=cut['projected_external']; new='Foundation.FirstOrder.Arithmetic.IOpen.Basic'
assert len(ext)==5 and new not in ext and all(v['present'] for v in ext.values())
# Count consequences only for the previously described bounded cut. The full
# Foundation provider ancestry and object companions remain unresolved.
out={'scope':'bounded source and lexical review only; no Lean, object authentication, transitive external closure or proof',
 'exact_one_line_prepend':True,'source_theorem_and_axiom_command_unchanged':True,
 'model_difference_ring_project_sources':len(sources),'model_difference_ring_leaves':len(leaves),
 'precedent_same_model_assumptions':True,'foundation_basic_publicly_imports_schemata':True,
 'old_lexical_missing_sources':old['projected_missing_sources'],'old_lexical_project_frontier':old['projected_frontier_objects'],
 'old_lexical_external_count':len(ext),'new_direct_external_module':new,
 'corrected_bounded_external_count':len(ext)+1,'new_external_object_path':str(obj),'new_external_object_sha256':sha(obj.read_bytes()),
 'temporary_source_and_object_availability_only':True}
print(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False))
