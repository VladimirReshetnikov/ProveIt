#!/usr/bin/env python3
"""Read saved three-leaf outcomes and check semantic fields; no candidate replay."""
from pathlib import Path
import argparse,hashlib,json
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--actual',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.actual.resolve().parent;r=json.loads(a.actual.read_text());p=Path(r['disposable_packet'])
 assert r['status']=='SELECTED_LEAVES_PASS' and r['inputs_unchanged'] and r['wall_cap_seconds_each']==60
 assert [j['name']for j in r['jobs']]==['seed3','action-variants','scanner-route']
 for j in r['jobs']:
  assert j['returncode']==0 and j['timeout'] is False and 0<j['seconds']<60
  assert sha(Path(j['stdout']))==j['stdout_sha256'] and sha(Path(j['stderr']))==j['stderr_sha256']
  assert Path(j['stderr']).stat().st_size==0
 for f,h in r['inputs_before'].items():assert h==r['inputs_after'][f]==sha(p/f)==sha(Path(r['source_packet'])/f)
 for item in r['outputs']:
  f=root/item['path'];assert f.stat().st_size==item['bytes'] and sha(f)==item['sha256']
 seed=json.loads((root/'results/seed3/seed3-replay.json').read_text());assert seed=={'status':'CLOSED_EQUALITY_CERTIFICATE_PASS','nodes':79,'rules':['G','K','S','gen','mp','rho1','rho2','rho6'],'native_output_code':3}
 v=json.loads((root/'results/action-variants.json').read_text());assert (v['status'],v['variants'],v['cylinders'],v['radius'],v['old_steps'],v['maximum_new_steps'],v['negative_control_rejected'])==('ALL_INDIVIDUAL_REWRITES_PROVED',62,3968,3,1,3,True)
 assert v['table_sha256']==sha(p/'data/k218.native.tm') and v['variants_sha256']==sha(p/'data/action-variants.txt')
 assert len(v['proofs'])==62 and all(x['maximum_steps']==3 for x in v['proofs'])
 s=json.loads((root/'results/scanner-route.json').read_text());t=s['startup'];assert s['status']=='STARTUP_AND_LOCAL_SCANNER_OBSTRUCTION_REPLAYED'
 assert s['table_sha256']==sha(p/'data/delete50.native.tm')
 assert (t['steps'],t['head'],t['gap'],t['pc_ones'],t['registers'],t['spares'])==(104082,-6,6,[],[4,3,0,0,3,0,0,0,0],[1]*59)
 phy=(6,2,0,4,3,7,8,5,1);vs=[0]*9
 for i,k in enumerate(phy):vs[k]=t['registers'][i]
 h=t['head'];header=h+64+t['gap'];support={h-1,header};pos=header+1
 for n in vs+t['spares']:
  pos+=1;support.update(range(pos,pos+n+1));pos+=n+1
 assert sorted(support)==t['support']
 c=s['scanner_checkpoint'];assert(c['accepted_steps'],c['short_steps'],c['state'],c['head'])==(288,286,34,10)
 assert 9 in c['support'] and 17 in c['support'] and not set(range(10,17)).intersection(c['support'])
 assert s['accepted_after_two_more_steps']=={'state':2,'head':8} and s['short_after_two_more_steps']=={'state':84,'head':10}
 assert s['accepted_primitive_endpoint_steps']==588 and s['abstract_source_reachability']=={'steps':2410,'ordinal':40,'registers':[7,0,6,0,4,0,0,0,0]}
 out={'status':'SAVED_SELECTED_SEMANTICS_REVIEW_PASS','actual':str(a.actual.resolve()),'actual_sha256':sha(a.actual),'jobs':3,'total_seconds':sum(j['seconds']for j in r['jobs']),'seed_proof':{'nodes':79,'code':3,'retained_K_S_theorem_schemas':'inherited; not rederived by this leaf'},'individual_rewrites':{'variants':62,'complete_cylinders':3968,'old_steps':1,'new_steps':3,'simultaneous_composition':'not established'},'scanner_obstruction':{'blank_steps':104082,'source_reachability_steps':2410,'accepted_local_steps':288,'short_local_steps':286,'seven_zero_run':True,'rejects':'the intended scanner/runtime argument, not every possible calibration'},'scope':'Own read-only saved-result/log/input-identity/complete-frame review. No second candidate execution, no fresh core-runtime/search/manifest/ancestor/proof-assistant claim.','reviewer_sha256':sha(Path(__file__))}
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
