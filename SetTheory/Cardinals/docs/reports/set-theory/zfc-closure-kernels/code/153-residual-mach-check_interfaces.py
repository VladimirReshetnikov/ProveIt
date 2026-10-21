#!/usr/bin/env python3
"""Unbounded whole-tape primitive refinement; this does not prove blank-run correctness."""
import argparse,hashlib,json,sys,time
from pathlib import Path
DEPS={
 'portable/build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
 'portable/source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
 'portable/runtime/vendor/symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
 'portable/runtime/vendor/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'portable/runtime/reference_results/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline221',type=Path,required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not sys.flags.optimize,'Run with assertions enabled'
 base=a.baseline221.resolve()
 for name,digest in DEPS.items():assert sha((base/name).read_bytes())==digest,('pinned dependency changed',name)
 sys.path.insert(0,str(base/'portable'));import build221 as b;import source_language as source
 sys.path.insert(0,str(base/'portable/runtime/vendor'));import symbolic_runtime as r
 table_raw=a.table.read_bytes();sites_raw=a.sites.read_bytes();T=b.read_table(table_raw);ss=json.loads(sites_raw);tree=source.tree(ss)
 states={q for q,bit in T};assert len(T)==2*len(states) and 254 not in states
 mp={int(q):int(z)for q,z in json.loads((base/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:
  if q not in mp:mp[q]=q+1000
 assert len(set(mp.values()))==len(mp) and mp[84]==96 and mp[254]==254
 M={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()};cases=[];used=set();expected=sum(2 if x[1]=='CD'else 1 for x in ss);start=time.monotonic();status='NOT_PROVED';a.output.mkdir(parents=True,exist_ok=True);failure=None
 try:
  lemmas,blocks=r.prove_blocks(M)
  for i,site in enumerate(ss):
   for positive in ((False,True)if site[1]=='CD'else(False,)):
    got=r.case(M,lemmas,site,positive);used.update(got.pop('rows'));got.pop('trace');cases.append({'index':i,'positive':positive,**got})
   if i%500==0:print('PROVED',i,len(cases),round(time.monotonic()-start,2),flush=True)
  assert len(cases)==expected;status='ALL_PRIMITIVE_INTERFACES_PROVED'
 except Exception as error:
  failure={'index':i,'site':site,'positive':positive,'reason':str(error)};print('FAILURE',failure,flush=True)
 inv={z:q for q,z in mp.items()}
 result={'status':status,'working_states':len(states),'transition_rows':len(T),'cases':len(cases),'expected_cases':expected,'symbolic_steps':sum(x['symbolic_steps']for x in cases),'table_sha256':sha(table_raw),'sites_sha256':sha(sites_raw),'driver_sha256':sha(Path(__file__).read_bytes()),'dependencies':DEPS,'source_metrics':source.metrics(tree),'used_native_rows':sorted((inv[q],bit)for q,bit in used),'seconds':time.monotonic()-start,'failure':failure,'scope':'Every supplied source leaf, both decrement guards; arbitrary natural primary registers, extra blank gap, first spare value, and remaining finite spare list; exact entire tape and positive finite duration. Mathematical symbolic checking, not proof-assistant kernel checking. Source semantics, equiconsistency and blank startup are separate obligations.'}
 (a.output/'cases.json').write_text(json.dumps(cases,indent=2)+'\n');(a.output/'runtime.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k not in ['used_native_rows','dependencies']},flush=True)
 return 0 if status=='ALL_PRIMITIVE_INTERFACES_PROVED'else 1
if __name__=='__main__':raise SystemExit(main())
