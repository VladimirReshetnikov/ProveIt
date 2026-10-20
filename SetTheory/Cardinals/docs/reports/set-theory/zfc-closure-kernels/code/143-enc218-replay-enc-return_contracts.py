"""Owned exact219 replay and full symbolic entry tapes for the new return.

Imports only the previously owned runtime kernel; received maps and tables are
inert data. This driver does not import or execute received source programs.
"""
from pathlib import Path
from collections import Counter
import sys,json,hashlib,time,argparse
import direct_screen as D
ROOT=D.D.parent
KERNEL=ROOT/'k223_merged_runtime_audit/runtime'
sys.path.insert(0,str(KERNEL));import symbolic_runtime as S
def canonical(x):return json.loads(json.dumps(x))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);args=ap.parse_args()
 assert __debug__ and not sys.flags.optimize
 p=D.BASE/'k219.native.tm';sp=D.BASE/'sites219.json';mpath=ROOT/'latest219_baseline/source132/portable/runtime/reference_results/legacy_mapping.json'
 assert D.H(p.read_bytes())=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
 assert D.H(sp.read_bytes())=='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
 assert D.H(mpath.read_bytes())=='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
 native=D.table(p);mp={int(q):int(z)for q,z in json.loads(mpath.read_text()).items()}
 for q in {q for q,b in native}|{254}:
  if q not in mp:mp[q]=q+1000
 assert len(mp)==len(set(mp.values())) and (mp[0],mp[84],mp[254])==(95,96,254)
 T={(mp[q],b):(w,m,mp[z])for(q,b),(w,m,z)in native.items()};sites=json.loads(sp.read_text());assert len(sites)==4744 and sum(1+(s[1]=='CD')for s in sites)==6167
 oldmp={int(q):int(z)for q,z in json.loads((ROOT/'k223_merged_runtime_audit/inputs/state_map.json').read_text())['k_to_legacy'].items()}
 assert all(mp[q]==oldmp[q]for q in mp.keys()&oldmp.keys())
 assert S.r.PHY==(6,2,0,4,3,7,8,5,1)
 # Full prefix-tree/data shape validation independent of the old source pin.
 paths={p for p,o,a in sites};prefix={p[:i]for p in paths for i in range(len(p))};assert len(paths)==4744 and len(prefix)==4743 and not paths&prefix
 assert all(p+b in paths|prefix for p in prefix for b in '01')
 lemmas,blocks=S.prove_blocks(T);original=S.State.step;captures={};case_index=0;current=None;rows=set();cases=[];began=time.monotonic()
 targetrows={(mp[103],1),(mp[113],0)}
 incoming={r for r,act in T.items()if act[2]==mp[302]};assert incoming==targetrows|{(mp[302],1)}
 def checked_step(self,table,proofs,clock,motion):
  key=self.key();q,d,left,right=key
  if q in {r[0]for r in targetrows}:
   src=right if d==1 else left
   if src and src[0][0]=='run' and (q,src[0][1])in targetrows:
    data=canonical(dict(state=q,direction=d,left=left,right=right));k=json.dumps(data,sort_keys=True)
    if k not in captures:captures[k]=dict(**data,first_case=case_index,site=current,multiplicity=0)
    captures[k]['multiplicity']+=1
  return original(self,table,proofs,clock,motion)
 S.State.step=checked_step
 for i,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   current=[i,site,positive];a=S.case(T,lemmas,site,positive);rows.update(a['rows']);a.pop('rows');a.pop('trace');cases.append(dict(index=i,positive=positive,**canonical(a)));case_index+=1
   if case_index%500==0:print(case_index,round(time.monotonic()-began,2),'captures',len(captures),flush=True)
   if args.limit and case_index>=args.limit:break
  if args.limit and case_index>=args.limit:break
 S.State.step=original
 tag='PILOT'if args.limit else'FULL'
 result=dict(status='PARTIAL_UNIVERSAL_RUNTIME'if args.limit else'PASS_FULL_UNIVERSAL_RUNTIME',cases=case_index,expected_cases=6167,rows=len(rows),rules=sum(c['symbolic_steps']for c in cases),minimum_duration=min(c['duration'][0]for c in cases),captures=len(captures),multiplicity=sum(c['multiplicity']for c in captures.values()),seconds=time.monotonic()-began,input_pins={str(p):D.H(p.read_bytes())for p in[p,sp,mpath,KERNEL/'symbolic_runtime.py',KERNEL/'independent_runtime.py']})
 if not args.limit:assert case_index==6167 and rows==set(T)
 D.dump(f'RETURN_{tag}_RESULT.json',result);D.dump(f'RETURN_{tag}_CONTRACTS.json',list(captures.values()));D.dump(f'RETURN_{tag}_CASES.json',cases);D.dump('NATIVE_TO_LEGACY.json',mp);D.dump('EXACT219_BLOCKS.json',blocks)
 print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
