#!/usr/bin/env python3
"""Replay the frozen Runtime193 two-edit, all-start startup corroboration."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args();out=a.output.resolve()
 assert out!=HERE.resolve(),'Choose a new output directory.'
 out.mkdir(parents=True,exist_ok=True)
 manifest=json.loads((HERE/'MANIFEST.json').read_text())
 for name,digest in manifest.items():assert sha(HERE/name)==digest,name
 old=json.loads((HERE/'receipt.json').read_text())
 records=[json.loads(x)for x in (HERE/'candidate_rewrites.jsonl').read_text().splitlines()]
 assert len(records)==old['candidate_rewrites']==346
 expected=''.join(f"{i} {r['state']} {r['read']} {' '.join(map(str,r['new']))}\n"for i,r in enumerate(records))
 assert expected==(HERE/'edits.tsv').read_text()
 controls=set()
 for line in (HERE/'runtime193.native.tm').read_text().splitlines():
  q,b,w,d,n=line.split();controls.add(int(q))
 assert len(controls)==193
 pairs=sum((x['state'],x['read'])!=(y['state'],y['read'])for i,x in enumerate(records)for y in records[i+1:])
 assert pairs==58485
 for r in records:assert (r['state']in controls and r['new'][2]in controls|{254})
 binary=out/'pair_startup'
 subprocess.run(['g++','-O3','-std=c++17',str(HERE/'pair_startup.cpp'),'-o',str(binary)],check=True)
 command=[str(binary),str(HERE/'runtime193.native.tm'),str(HERE/'edits.tsv'),
          str(HERE/'startup_any_frame_templates.tsv'),'200000','-1']
 with (out/'hits.jsonl').open('w')as hits,(out/'run.log').open('w')as log:
  subprocess.run(command,check=True,stdout=hits,stderr=log)
 line=(out/'run.log').read_text().strip().splitlines()[-1]
 match=re.fullmatch(r'DONE pairs (\d+) sims (\d+) ticks (\d+) halts (\d+) rays (\d+) limits (\d+) successes (\d+) seconds ([0-9.]+)',line)
 assert match,line
 names=['pairs','simulations','literal_transitions','halts','outward_rays','bounded_runs','complete_frames','elapsed_seconds']
 statistics={k:(float(v)if k=='elapsed_seconds'else int(v))for k,v in zip(names,match.groups())}
 for name,value in old['statistics'].items():
  if name!='elapsed_seconds':assert statistics[name]==value,(name,statistics[name],value)
 assert not(out/'hits.jsonl').read_bytes()
 result={'status':'PASS','statistics':statistics,'command':command,
         'program_sha256':sha(HERE/'pair_startup.cpp'),
         'scope':old['logical_scope']}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
