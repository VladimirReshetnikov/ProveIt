#!/usr/bin/env python3
"""Focused exact symbolic cases for changed shared108 and added CI-right entries."""
from pathlib import Path
import hashlib,json,sys,time,argparse
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--patched',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not a.out.exists();sys.dont_write_bytecode=True
 sys.path[:0]=[str(HERE/'code'),str(a.baseline/'portable/runtime/vendor')]
 import source_language as s,build221 as b,symbolic_runtime as r
 deps={a.baseline/'portable/runtime/vendor/symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',a.baseline/'portable/runtime/vendor/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'}
 assert all(sha(p)==h for p,h in deps.items())
 mapfile=a.baseline/'portable/runtime/reference_results/legacy_mapping.json';assert sha(mapfile)=='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
 records=json.loads((a.patched/'result.json').read_text())['records'];a.out.mkdir(parents=True);results=[]
 for rec in records:
  sp=Path(rec['source_path']);assert sha(sp)==rec['source_sha256'];sites=json.loads(sp.read_text());tree=s.tree(sites)
  for variant,key,pin in [('original','old_path','old_sha256'),('shared108','new_path','new_sha256')]:
   p=Path(rec[key]);assert sha(p)==rec[pin];table=b.read_table(p.read_bytes());g,paths=b.decoder_map(table,tree)
   touched={q for q,bit,before,after in rec['edits']}
   prefixes=[pref for q in touched if q in paths for pref in paths[q]]
   indices=[i for i,(path,op,arg) in enumerate(sites) if any(path.startswith(pref) for pref in prefixes) or op=='CI' and arg in(5,6) and path.endswith('1')]
   # Existing concrete failing CD6-zero leaf must run before the rest.
   first=next((i for i,site in enumerate(sites) if site==['1110100100111011110000100','CD',6]),None)
   if first is not None:indices=[first]+[i for i in indices if i!=first]
   mp={int(q):int(z) for q,z in json.loads(mapfile.read_text()).items()}
   for q in {q for q,bit in table}|{254}:mp.setdefault(q,q+1000)
   assert len(set(mp.values()))==len(mp)
   legacy={(mp[q],bit):(w,d,mp[z]) for(q,bit),(w,d,z)in table.items()};lemmas,blocks=r.prove_blocks(legacy)
   passed=[];fail=None;start=time.monotonic()
   for i in indices:
    for positive in((False,True) if sites[i][1]=='CD' else(False,)):
     try:
      ans=r.case(legacy,lemmas,sites[i],positive);ans.pop('trace');ans['rows']=sorted(ans['rows']);passed.append(dict(index=i,site=sites[i],positive=positive,**ans))
     except (AssertionError,KeyError) as exc:
      fail=dict(index=i,site=sites[i],positive=positive,reason=repr(exc));break
    if fail:break
   row=dict(hit=rec['hit'],variant=variant,status='TARGETED_CASES_PASS' if fail is None else 'NOT_PROVED',table_sha256=sha(p),source_sha256=sha(sp),indices=indices,passed_guards=len(passed),failure=fail,seconds=time.monotonic()-start,scope='Only explicitly selected changed-entry cases; no complete runtime/startup claim.')
   d=a.out/f'hit{rec["hit"]:02}-{variant}';d.mkdir();dump(d/'cases.json',passed);dump(d/'result.json',row);results.append(row)
   print({k:row[k] for k in('hit','variant','status','passed_guards','seconds')},'failure',None if fail is None else(fail['index'],fail['site'],fail['positive']),flush=True)
 dump(a.out/'result.json',dict(status='TARGETED_ENTRY_CHECKS_COMPLETE',results=results,dependencies={str(p):h for p,h in deps.items()}))
if __name__=='__main__':main()
