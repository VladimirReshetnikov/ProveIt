#!/usr/bin/env python3
"""Check the observed raw frame and seek a concrete source-mask counterexample.

This is a finite diagnostic, never a theory-to-machine calibration theorem.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE));import check_joint_fold as tables

def need(v,msg):
 if not v:raise ValueError(msg)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def describe(conf,inv):
 q,h,ones=conf;return {'native_state':inv[q],'head':h,'ones':sorted(ones)}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--packet-root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.packet_root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
 sys.path.insert(0,str(root/'core217/vendor'));import independent_runtime as r
 mask_path=root/'machine-search/results/masked_source_certificate/invariants.json'
 data=json.loads(mask_path.read_text());source_path=root/'baseline218/sites218.json';sites=json.loads(source_path.read_text());need(data['ordered']==sites,'source-mask binding')
 native,start=tables.read(root/'core217/core.native.tm');native[51,0]=(1,-1,6)
 candidate=out/'raw-frame-exploration.native.tm';candidate.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(native.items())))
 q=h=0;ones=set()
 for tick in range(532731):
  w,d,q=native[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 need((q,h)==(84,-17),'raw startup endpoint')
 need(r.clean_dispatch(96,h,ones),'raw startup complete clean-frame predicate')
 need(not any(h<=x<h+64 for x in ones),'raw startup empty source address')
 expected_raw={x-17 for x in r.frame('',[0,0,1,0,0,0,0,0,0],[1]*253,1)}
 raw_exact=ones==expected_raw
 # Decode actual words rather than assuming the spare values from the trace.
 header=min(x for x in ones if x>=h+64);p=header+1;vals=[]
 while p<=max(ones):
  need(p not in ones and p+1 in ones,'word delimiter');p+=1;n=0
  while p in ones:n+=1;p+=1
  vals.append(n-1)
 raw={'steps':532731,'state':q,'head':h,'gap':header-h-64,'logical_registers':[vals[j]for j in r.PHY],'spares':vals[9:],'one_cells':len(ones),'exact_expected_one_spare_frame':raw_exact}
 mp={int(q):int(z)for q,z in json.loads((root/'core217/vendor/legacy_mapping.json').read_text()).items()};mp.update({301:1301,302:1302});inverse={z:q for q,z in mp.items()};tab={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in native.items()}
 checked=0;failure=None
 for scenario in range(8):
  for i,(site,masks)in enumerate(zip(sites,data['states'])):
   if masks is None:continue
   for positive in((False,True)if site[1]=='CD'else(False,)):
    if site[1]=='CD'and not(masks[site[2]]&(510 if positive else 1)):continue
    regs=[]
    for j,mask in enumerate(masks):
     vals=[v for v in range(8)if mask>>v&1]+([8,9,20]if mask&256 else[])
     if site[1]=='CD'and j==site[2]:vals=[v for v in vals if(v>0)==positive]
     k=0 if scenario==0 else len(vals)-1 if scenario==1 else (i*7+j*3+scenario)%len(vals)
     regs.append(vals[k])
    spares=[1]*(scenario%5+1);gap=scenario%3;want=r.expected(site,regs,spares,gap);actual,steps,trace=r.run(tab,site[0],regs,spares,gap,100000,True)
    good=actual[0]==254 if want is None else actual==want[0];checked+=1
    if not good:
     failure={'scenario':scenario,'site_index':i,'site':site,'positive':positive,'registers':regs,'register_masks':masks,'spares':spares,'gap':gap,'steps':steps,'initial_one_cells':sorted(r.frame(site[0],regs,spares,gap)),'actual':describe(actual,inverse),'expected':{'halt':True}if want is None else describe(want[0],inverse),'expected_logical':None if want is None else want[1],'trace_file':'raw-frame-counterexample-trace.json'}
     (out/failure['trace_file']).write_text(json.dumps([[tick,inverse[q],h,b,w,d,inverse[z]]for tick,q,h,b,w,d,z in trace],indent=2)+'\n');break
   if failure:break
  if failure:break
 result={'status':'SOURCE_MASK_RUNTIME_COUNTEREXAMPLE'if failure else'FINITE_SOURCE_MASK_SAMPLES_PASS_ONLY','candidate_sha256':digest(candidate),'source_sha256':digest(source_path),'mask_certificate_sha256':digest(mask_path),'raw_frame':raw,'checked_cases':checked,'counterexample':failure,'scope':'The changed table does produce the reported clean blank-start frame. A counterexample shows that the existing source-mask primitive implementation theorem cannot be inherited for this table. It does not prove a statement about all executions from the alternate raw seed; that would require a separate reachable-state analysis.'}
 (out/'raw-frame-diagnostic.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('raw_frame','counterexample')},indent=2));print('COUNTEREXAMPLE',None if failure is None else{i:failure[i]for i in ['site_index','site','registers','spares','gap','steps']})
if __name__=='__main__':main()
