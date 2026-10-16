#!/usr/bin/env python3
"""Quick reproducibility gate; does not rerun the 6.3-billion-move search.
Verifies frozen source hashes, all 8,391 prepared-runtime affine cases, the
three exact guarded detours, the abstract invariant, and every short blank-ray
certificate. It recomputes all blank first-write classes and report totals.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
from emit_runtime_variants import rows
import verify_abstract_certificate
ROOT=Path(__file__).parent

def main():
 if (ROOT/'MANIFEST.sha256').exists():
  for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
   digest,path=line.split('  ',1)
   assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
 provenance=json.loads((ROOT/'PROVENANCE.json').read_text())
 for entry in provenance['files']:
  p=ROOT/entry['file'];assert p.stat().st_size==entry['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256']
 base=rows();T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items()}
 ns=executor(T,ROOT/'sources/symexec.py');cs=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
 for c in cs:assert check(ns,c,fuel=500)
 manifests=json.loads((ROOT/'runtime_variant_manifest.json').read_text())
 for spec in manifests:
  p=ROOT/spec['file'];assert hashlib.sha256(p.read_bytes()).hexdigest()==spec['sha256']
  candidate,start,working,terminals,_=parse_table(p)
  assert start==96 and len(working)==252 and len(candidate)==504 and terminals==[254]
  delta={key:value for key,value in candidate.items() if value!=base[key]}
  assert delta==({} if 'detour' not in p.name else {(49,1):(1,'L',spec['delta_49_read1'][2])})
 # Finite transition facts prove the local three-step macro equivalence.
 incoming49=[(list(key),list(value)) for key,value in base.items() if value[2]==49]
 assert sorted(incoming49)==[([34,0],[0,'R',49]),([79,0],[0,'R',49])]
 assert base[70,1]==(0,'R',64)
 for r in (54,66,114):assert base[r,0]==(0,'R',70)
 detours={'guard':'state=49, current cell=1, left cell=0','original':[0,'R',64],
          'alternatives':[[1,'L',r] for r in (54,66,114)],'base_steps':1,'detour_steps':3,
          'left_zero_guard_follows_from_all_incoming_edges':True,'incoming_edges':incoming49,
          'scope':'Finite table facts plus the elementary simulation proof in README; same blank-start halting as runtime252, whose consistency connection is not established.'}
 (ROOT/'guarded_detour_verification.json').write_text(json.dumps(detours,indent=2)+'\n')
 verify_abstract_certificate.main()
 search=json.loads((ROOT/'single_row_results.json').read_text());survivors=search['survivors']
 assert search['tested']==449*(4*253-1)==453939 and len(survivors)==707
 records=[json.loads(line) for line in (ROOT/'single_row_boot_results.jsonl').read_text().splitlines()]
 classifications={x['candidate']:x for x in records if x['type']=='classification'}
 runs=[x for x in records if x['type']=='result'];frames=[x for x in records if x['type']=='frame']
 assert len(classifications)==707 and not frames
 run_index={(x['candidate'],x['start']):x for x in runs};assert len(run_index)==len(runs)
 ray_count=0;firstwrite_starts=0;zero_only=0
 for i,mut in enumerate(survivors):
  a,b,w,d,q=mut;tab=base.copy();tab[a,b]=(w,d,q)
  groups={};cycles=[]
  for st in sorted({s for s,bit in tab}):
   p=st;seen=set()
   while p not in seen:
    assert (p,0) in tab,('halt before first write',i,st)
    seen.add(p);write,move,target=tab[p,0]
    if write:groups.setdefault(p,[]).append(st);break
    p=target
   else:cycles.append(st)
  cl=classifications[i];assert cl['mutation']==mut
  assert sorted(groups)==cl['representatives'];assert len(cycles)==cl['zero_only_cycle_starts']
  assert sum(map(len,groups.values()))+len(cycles)==252
  firstwrite_starts+=sum(map(len,groups.values()));zero_only+=len(cycles)
  for st in groups:
   run=run_index[i,st];assert run['frames']==0
   if run['outcome']=='fuel_limit':assert run['steps']==3000000
   else:
    assert run['outcome']=='blank_ray_self_loop'
    p=st;h=0;tape=set()
    for _ in range(run['steps']):
     write,move,p=tab[p,int(h in tape)]
     if write:tape.add(h)
     else:tape.discard(h)
     h+=1 if move=='R' else -1
    assert (p,h,len(tape))==(run['state'],run['head'],run['ones'])
    assert h not in tape
    write,move,target=tab[p,0];assert target==p
    assert not any(x>=h for x in tape) if move=='R' else not any(x<=h for x in tape)
    ray_count+=1
 assert len(runs)==4951 and ray_count==2845
 counts=dict(Counter(x['outcome'] for x in runs));assert counts=={'blank_ray_self_loop':2845,'fuel_limit':2106}
 summary={'operational_states_per_candidate':252,'affine_runtime_cases_checked':len(cs),'all_four_prepared_tables_verified':True,
          'single_row_mutations_tested':search['tested'],'affine_accepted_mutations':len(survivors),'initial_state_choices':707*252,
          'zero_only_cycle_initial_states':zero_only,'starts_reducing_to_first_write':firstwrite_starts,'distinct_first_write_representatives':len(runs),
          'blank_run_outcomes':counts,'maximum_ray_certificate_prefix':max(x['steps'] for x in runs if x['outcome']=='blank_ray_self_loop'),
          'simulation_fuel_per_representative':3000000,'total_recorded_moves':sum(x['steps'] for x in runs),'valid_gap40_frames':0,
          'full_long_runs_repeated_by_quick_gate':False,'scope':'Source integrity, symbolic runtime audit, exact short certificates and fixed-point certificate checked. Capped long runs are archived experimental observations; rerun the C++ search to reproduce them.'}
 (ROOT/'quick_verification.json').write_text(json.dumps(summary,indent=2)+'\n')
 (ROOT/'search_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
