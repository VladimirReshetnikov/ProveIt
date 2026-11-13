#!/usr/bin/env python3
"""Check selected 196-state archive tables and classify rooted machine graphs."""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
# status, archive, member, raw SHA-256, start, halt
TABLES = [
 ('upstream','conpa_tm_comparison_and_reduction_search.zip','conpa_tm_comparison_and_reduction_search/machines/published_pa196.tm','e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8',0,196),
 ('experimental','conpa_tm_comparison_and_reduction_search.zip','conpa_tm_comparison_and_reduction_search/machines/experimental_mp_result_in_h_196.tm','893f08672746ea1c281fda7de4ecc7c8a75fa1f896f2255c9c00e345c37aaaca',0,196),
 ('experimental','conpa_tm_comparison_and_reduction_search.zip','conpa_tm_comparison_and_reduction_search/machines/experimental_mp_without_zero_push_196.tm','3d7f91e548f8a21ed4d6eecdc1f1299d960b612912bf9a6bf7b74870c5c9f11a',0,196),
 ('rejected','conpa_tm_comparison_and_reduction_search.zip','conpa_tm_comparison_and_reduction_search/rejected/REJECTED_shift_layout.tm','db5cd7df1475e4c2edf43f856493e211ed116a7a998eaada741515840424736b',0,196),
 ('rejected','conpa_tm_comparison_and_reduction_search.zip','conpa_tm_comparison_and_reduction_search/rejected/REJECTED_combined_layout.tm','d3a049def261732d1c1aa99a48de63c00a1241f02b629b2ae45d445bba6c9527',0,196),
 ('candidate','pa_tm_research_2026-11-13.zip','pa_tm_research_2026-11-13/alternative196/alternative196.tm','aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95',0,196),
 ('candidate','pa_tm_extended_research_2026-11-13.zip','pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd3.tm','d5c1c2c69082971b23cc42da4c36f82f33ffb09f6482ca2f1c1ac6ab405249ca',0,196),
 ('candidate','pa_tm_extended_research_2026-11-13.zip','pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd4.tm','2be1986cbbac0c6e98cc4e515d83c2b9c7b063c3ac43fe30e919ce9d54e5c87d',0,196),
 ('candidate','pa_tm_extended_research_2026-11-13.zip','pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd5.tm','4433af83b56864fd5da9971e1bdee7236ceba5519160648f67ea8cb509558498',0,196),
 ('candidate','pa_tm_extended_research_2026-11-13.zip','pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd6.tm','2db09bb057682bdef3ded53dd086c2b24a3800ac74e4ae8a048eaf14b59b0536',0,196),
 ('candidate','pa_tm_comparison_and_reductions.zip','pa_tm_research/rotated196/candidate/data/rotated196.tm','25d686ab95f58b1d9eb1f75cb0960ca9f16640a1536140961c90ba8e103e8413',0,196),
 ('candidate','pa_tm_comparison_and_reductions.zip','pa_tm_research/rotated196/candidate-macro62/data/rotated196-macro62.tm','591f4240775256349f85a3d99708ba8ebd7e245779271c1cb2244cf04ce87e76',0,196),
 ('candidate','pa_consistency_research.zip','pa_consistency_research/data/variant196.tm','1ab0fd1fe7b727cc8841fcb32a2f20bec956d44b9b43b151c6a505da01721790',0,196),
 ('candidate','conpa_tm_comparison_and_search.zip','conpa_tm_study/research196/accepted196_register_swap/pa196_register_AD_swap.tm','3968e6733b30e0812b595062dc4c7e8355df74f42a61177af54917d873465625',0,196),
 ('candidate','pa_consistency_reduction.zip','pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm','e212e359837cff6d1b3ab665855b0e9b4a2b471d23e77db447680d494d943b80',0,196),
 ('candidate','pa_consistency_reduction.zip','pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm','5e7e8daf0fbd91d27389de054023bc5959e0246f4001c0ec1381dc3f53a55dac',0,196),
 ('candidate','pa_consistency_research_2026-11-13 (2).zip','pa_consistency_research_2026-11-13/rotated196/machine.tm','b9873b89df4189414d0f443922ca9227bf2f76d8c81a0d0951c06cd608d6a90b',0,196),
 ('candidate','conpa_tm_study_2026-11-13.zip','conpa_tm_study/machines/h_only_mp_h.tm','bd74754d75e7b8ba97fa7bfc104374de33ae603fc183ae7f08f053ab8c9ea592',0,196),
]

def need(ok, message):
    if not ok: raise ValueError(message)

def machine(data, start, halt):
    rows = {}
    for line in data.decode('ascii').splitlines():
        if not line.strip() or line.startswith('#'): continue
        q,b,w,d,n = line.split()
        q,b,w,n = map(int,(q,b,w,n))
        need(b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows,'invalid row')
        rows[q,b] = (w,d,n)
    states = {q for q,b in rows}
    need(len(states)==196 and start in states and halt not in states and
         set(rows)=={(q,b) for q in states for b in (0,1)} and
         all(n in states or n==halt for w,d,n in rows.values()), 'invalid 196-state table')
    # Canonical traversal reads transition 0 then 1 at each discovered state.
    index={start:0}; order=[start]; canonical=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b]
            if n in states and n not in index:
                index[n]=len(index); order.append(n)
            canonical.append((w,d,-1 if n==halt else index[n]))
    need(len(order)==196, 'not all 196 states are graph-reachable')
    return sha256(json.dumps(canonical,separators=(',',':')).encode()).hexdigest()

def checked_machine(data, start, halt, member):
    try:
        return machine(data,start,halt)
    except ValueError as error:
        raise ValueError(member + ': ' + str(error)) from error

def main():
    result=[]
    for status,archive_name,member,digest,start,halt in TABLES:
        with ZipFile(ROOT/'docs/incoming'/archive_name) as archive:
            data=archive.read(member)
        need(sha256(data).hexdigest()==digest, 'changed archive member: '+member)
        result.append({'status':status,'archive':archive_name,'member':member,'sha256':digest,
                       'start':start,'halt':halt,'graph_class_sha256':checked_machine(data,start,halt,member)})
    grouped=defaultdict(list)
    for x in result:grouped[x['graph_class_sha256']].append(x['member'])
    out={'tables':result,'graph_class_count':len(grouped),'table_count':len(result),
         'scope':'Selected reported candidates and rejected controls; graph census does not prove halting equivalence or iPRA results.'}
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__ == '__main__': main()
