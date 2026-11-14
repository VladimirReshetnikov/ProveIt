#!/usr/bin/env python3
"""Deterministically rebuild U218 and its documented intermediate tables.

No synthesis optimizer, solver, external repository, or network is used.
The provisional table is a rejected artifact included solely to replay the
specific routing repair. Only final U218 carries the published endpoint.
"""
from pathlib import Path
import argparse,hashlib,json
from table_io import require,parse,encode

K215_SHA256='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
U222_SHA256='88a9c5ea637560bf58dba612d598663213884d7bb7981230164bc058babaa427'
SOURCE_SHA256='bc70b28ff4628db5b9b0c9bd87f560697223e4887f2568b0ece801906713db8f'
NATIVE_SHA256='366cf96800bd4299de831355a80092394462278f0b62db1e19c167ca5f8b2a30'
DENSE_SHA256='225709a399367b5b1683ec0dc35994929184e4c9c1dcd638771a8a5c3efda953'
PARENT_ARCHIVE_SHA256='d23e80857214900f8e0806f03f6df752af501dd0108eb92c6ed7a49795802652'

def sha(raw):return hashlib.sha256(raw).hexdigest()

def validate(T,count,digest):
    raw=encode(T);parse(raw);require(len(T)==2*count,'Wrong stage census')
    require(sha(raw)==digest,'Stage hash mismatch');return raw

def delta(before,after,name):
    return {'stage':name,'from_working_states':len(before)//2,'to_working_states':len(after)//2,
      'changed_rows':[{'key':list(k),'old':list(before[k]),'new':list(after[k])}for k in sorted(before.keys()&after.keys())if before[k]!=after[k]],
      'added_rows':[[*k,*after[k]]for k in sorted(after.keys()-before.keys())],
      'removed_rows':[[*k,*before[k]]for k in sorted(before.keys()-after.keys())]}

def build(baseline,source,recipe,out):
    raw=baseline.read_bytes();src=source.read_bytes();r=json.loads(recipe.read_text())
    require(sha(raw)==r['baseline_sha256']==K215_SHA256,'Wrong K215 input')
    require(sha(src)==r['source_sha256']==SOURCE_SHA256,'Wrong source input')
    original=parse(raw);require(len(original)==430,'Wrong K215 census')
    patches=r['changed_or_added_rows'];require(len({tuple(x[:2])for x in patches})==len(patches),'Duplicate patch row')
    provisional=dict(original)
    for q,b,w,d,z in patches:
        require(b in(0,1)and w in(0,1)and d in(-1,1),'Invalid patch row')
        provisional[q,b]=(w,d,z)
    removed=set(r['removed_baseline_states'])
    provisional={k:v for k,v in provisional.items()if k[0]not in removed}
    stage0=validate(provisional,219,r['provisional_sha256'])
    repaired=dict(provisional)
    require(r['repair_retarget_rows']==[[q,0,0,1,507]for q in(18,134,188)],'Wrong repair redirects')
    require(r['repair_added_rows']==[[507,0,0,1,90],[507,1,1,1,61]],'Wrong repair clone')
    for q,b,w,d,z in r['repair_retarget_rows']+r['repair_added_rows']:repaired[q,b]=(w,d,z)
    stage1=validate(repaired,220,r['repaired220_sha256'])
    untagged={(q,b):(w,d,209 if z==200 else z)for(q,b),(w,d,z)in repaired.items()if q!=200}
    branch=validate(untagged,219,r['untagged219_sha256'])
    require(r['tagged_fold']=={'removed':507,'representative':182,'changed_row':[182,0,0,-1,209]},'Wrong tagged fold recipe')
    tagged={(q,b):(w,d,182 if z==507 else z)for(q,b),(w,d,z)in repaired.items()if q!=507}
    tagged[182,0]=(0,-1,209)
    stage2=validate(tagged,219,r['tagged219_sha256'])
    require(r['zero_fold']=={'removed':200,'representative':209},'Wrong zero fold recipe')
    final={(q,b):(w,d,209 if z==200 else z)for(q,b),(w,d,z)in tagged.items()if q!=200}
    native=validate(final,218,r['native_sha256']);require(sha(native)==NATIVE_SHA256,'Wrong final native hash')
    states=sorted({q for q,b in final});rename={q:i for i,q in enumerate(states)};rename[254]=218
    require(rename[0]==0,'Start not preserved')
    D={(rename[q],b):(w,d,rename[z])for(q,b),(w,d,z)in final.items()};dense=encode(D);parse(dense,218)
    require(sha(dense)==r['dense_sha256']==DENSE_SHA256,'Wrong dense bytes')
    inverse={v:k for k,v in rename.items()}
    require({(inverse[q],b):(w,d,inverse[z])for(q,b),(w,d,z)in D.items()}==final,'Dense bijection fails')
    mapping={'native_to_dense':{str(q):v for q,v in sorted(rename.items())},'dense_to_native':{str(v):q for v,q in sorted(inverse.items())},'start':0,'native_halt':254,'dense_halt':218,'removed_native_states':[200,507]}
    summary={'status':'EXACT_U218_RECONSTRUCTION_AND_RELABELING_PASS','working_states':218,'transitions':436,
      'alphabet':[0,1],'tapes':1,'heads':1,'moves':['L','R'],'blank_symbol':0,'initial_state':0,'native_halt':254,'dense_halt':218,
      'baseline_K215_sha256':K215_SHA256,'parent_U222_sha256':U222_SHA256,'parent_archive_sha256':PARENT_ARCHIVE_SHA256,
      'source_sha256':SOURCE_SHA256,'native_sha256':NATIVE_SHA256,'dense_sha256':DENSE_SHA256,'source_occurrences':len(json.loads(src)),'source_dag_nodes':202,'verified_untagged219_sha256':sha(branch),
      'stages':[{'name':'provisional219','states':219,'status':'REJECTED_ROUTING_ERROR','sha256':sha(stage0)},{'name':'repaired220','states':220,'status':'ROUTING_REPAIR_INTERMEDIATE','sha256':sha(stage1)},{'name':'tagged219','states':219,'status':'GUARDED_STUTTERING_INTERMEDIATE','sha256':sha(stage2)},{'name':'U218','states':218,'status':'FINAL_MACHINE','sha256':sha(native)}],
      'special_native_to_dense':{str(q):rename[q]for q in(18,61,67,76,84,90,112,133,134,151,157,172,173,182,188,209,254)}}
    deltas={'status':'EXACT_LITERAL_STAGE_DELTAS','stages':[delta(original,provisional,'K215 to rejected provisional219'),delta(provisional,repaired,'routing repair to220'),delta(repaired,tagged,'tagged fold to219'),delta(tagged,final,'known-zero fold to218'),delta(repaired,untagged,'alternate known-zero fold to219'),delta(untagged,final,'alternate tagged fold to218')]}
    out.mkdir(parents=True,exist_ok=True)
    (out/'table_deltas.json').write_text(json.dumps(deltas,indent=2)+'\n')
    for name,data in [('u218.native.tm',native),('u218.tm',dense),('sites.json',src),('provisional219.native.tm',stage0),('repaired220.native.tm',stage1),('tagged219.native.tm',stage2),('untagged219.native.tm',branch)]:
        (out/name).write_bytes(data)
    for name,data in [('state_map.json',mapping),('machine_summary.json',summary)]:
        (out/name).write_text(json.dumps(data,indent=2)+'\n')
    return summary

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--baseline',type=Path,required=True);p.add_argument('--source',type=Path,required=True);p.add_argument('--recipe',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    print(json.dumps(build(a.baseline,a.source,a.recipe,a.output),indent=2))
if __name__=='__main__':main()
