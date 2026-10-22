#!/usr/bin/env python3
# SPDX-License-Identifier: MIT-0
"""Own batch215 exact recovery. Delivery contents and checksum manifests remain inert."""
import argparse
from collections import Counter
import hashlib,io,json,re,subprocess,zipfile
from pathlib import Path,PurePosixPath
ARRIVAL='1b16269c48e54b0e5aff35caa645f392f9c019af'
HOST='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
EXPECTED_ARCHIVES=[{'number': 1, 'source': 193, 'archive_path': 'docs/incoming/K215_Proof_Simplification (2).zip', 'archive_blob': 'd07ea108bc48c4deb3824b1af612bfc43b72f1c0', 'archive_sha256': '8014fbcaf3aa4df315ef8c7bead92d7b754d87e2fd914e5ccc50396e6f64310f', 'archive_bytes': 654913, 'member_count': 258, 'member_bytes': 1542469}, {'number': 2, 'source': 194, 'archive_path': 'docs/incoming/K215_Proof_Simplification_2026-10-22.zip', 'archive_blob': 'f779cc031d92c0df5c63592a30f251f3b6e3c253', 'archive_sha256': 'f691874136f7e328c760049aa759ce2a831150f6ed0ddbd28b17d9f2531f466d', 'archive_bytes': 1436524, 'member_count': 250, 'member_bytes': 12845215}]
COUNTS={'git': 231, 'placed': 178, 'arrival_member': 50, 'delivery_member': 49}
def require(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def safe(name):
 require(isinstance(name,str) and bool(name),'Empty/non-string path')
 p=PurePosixPath(name)
 require(not p.is_absolute() and '..' not in p.parts and '\\' not in name and
   not re.match(r'^[A-Za-z]:',name) and not any(ord(c)<32 for c in name),'Unsafe path: '+name)
 return name
def clean_hash(repo,path,data):
 safe(path)
 out=subprocess.check_output(['git','-C',str(repo),'hash-object','--stdin','--path='+path],input=data)
 value=out.decode().strip();require(re.fullmatch('[0-9a-f]{40}',value) is not None,'Invalid Git clean hash')
 return value

def placed_bytes(repo,path,actual,original):
 if actual==original:return actual,False
 require(clean_hash(repo,path,actual)==clean_hash(repo,path,original),
         'Placed content differs beyond existing Git attributes: '+path)
 return original,True

class Git:
 def __init__(self,repo):
  self.p=subprocess.Popen(['git','-C',str(repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
  self.cache={}
 def read(self,commit,path):
  require(re.fullmatch('[0-9a-f]{40}',commit) is not None,'Non-immutable Git ref')
  q=commit+':'+safe(path)
  if q in self.cache:return self.cache[q]
  self.p.stdin.write((q+'\n').encode());self.p.stdin.flush()
  line=self.p.stdout.readline().decode().strip().split()
  require(len(line)==3 and line[1]=='blob','Missing Git blob '+q)
  n=int(line[2]);b=self.p.stdout.read(n)
  require(len(b)==n and self.p.stdout.read(1)==b'\n','Truncated Git response')
  self.cache[q]=b;return b
 def close(self):
  self.p.stdin.close();self.p.stdout.close();require(self.p.wait(timeout=10)==0,'Git reader failed')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,default=Path.cwd());ap.add_argument('--map',type=Path)
 modes=ap.add_mutually_exclusive_group(required=True);modes.add_argument('--verify-only',action='store_true');modes.add_argument('--out',type=Path)
 ap.add_argument('--result',type=Path)
 ap.add_argument('--planned-copy-map',type=Path,help='Planning only: read new payload from the exact external scratch paths in this map; makes no placed-file claim.')
 args=ap.parse_args();repo=args.repo.resolve();mp=args.map or repo/HOST/'data/intake215-placement.json'
 raw=mp.read_bytes();m=json.loads(raw)
 require((m['batch'],m['sources'],m['member_count'],m['member_bytes'])==(215,list(range(193,195)),508,14387684),'Wrong batch boundary')
 require(m['arrival_commit']==ARRIVAL and m['counts']==COUNTS,'Wrong arrival/routes')
 identities=[{k:a[k] for k in ['number','source','archive_path','archive_blob','archive_sha256','archive_bytes','member_count','member_bytes']} for a in m['archives']]
 require(identities==EXPECTED_ARCHIVES,'Wrong archive identities/order')
 require([r['manuscript'] for r in m['members']]==sorted(r['manuscript'] for r in m['members']),'Reordered archive members')
 planned={}
 if args.planned_copy_map:
  require(args.verify_only,'Scratch map allowed only in verify mode')
  pm=json.loads(args.planned_copy_map.read_text());planned={p['target']:p for p in pm['files']}
  require(len(planned)==178 and set(planned)=={r['path'] for r in m['members'] if r['route']=='placed'},'Incomplete planned payload')
 g=Git(repo);recovered={};actual_routes=Counter();total=0;attribute_equivalent=[]
 try:
  for a in EXPECTED_ARCHIVES:
   archive=g.read(ARRIVAL,a['archive_path'])
   require(len(archive)==a['archive_bytes'] and sha(archive)==a['archive_sha256'],'Changed arrival')
   require(hashlib.sha1(b'blob '+str(len(archive)).encode()+b'\0'+archive).hexdigest()==a['archive_blob'],'Wrong archive Git identity')
   with zipfile.ZipFile(io.BytesIO(archive)) as z:
    infos=z.infolist();names=[safe(i.filename) for i in infos]
    require(len(names)==len(set(names))==len({n.casefold() for n in names}),'Duplicate/colliding archive name')
    require(all(not (i.flag_bits&1) and ((i.external_attr>>16)&0o170000)!=0o120000 for i in infos),'Encrypted/symlink member')
    files=[i for i in infos if not i.is_dir()]
    rows=[r for r in m['members'] if r['manuscript']==a['number']]
    require([r['member'] for r in rows]==[i.filename for i in files],'Missing/reordered member')
    for r in rows:
     require(r['source']==a['source'],'Wrong source number')
     route=r['route'];name=r['member']
     if route=='git':data=g.read(r['commit'],r['path'])
     elif route=='delivery_member':
      key=(r['target_manuscript'],r['target_member']);require(key in recovered,'Unknown/forward alias');data=recovered[key]
     elif route=='arrival_member':data=z.read(name)
     elif route=='placed':
      path=safe(r['path'])
      if planned:
       q=planned[path];require((q['sha256'],q['bytes'],q['git_blob'],q['manuscript'],q['member'])==(r['sha256'],r['bytes'],r['git_blob'],r['manuscript'],name),'Planned binding changed');f=Path(q['source'])
      else:f=repo/path
      require(f.is_file() and not f.is_symlink(),'Missing/unsafe payload '+str(f))
      data,equivalent=placed_bytes(repo,path,f.read_bytes(),z.read(name))
      if equivalent:attribute_equivalent.append(path)
     else:raise ValueError('Unknown route '+route)
     require(len(data)==r['bytes'] and sha(data)==r['sha256'],'Member identity differs '+name)
     require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob'],'Wrong member Git identity')
     require(data==z.read(name),'Recovered bytes differ '+name)
     recovered[(a['number'],name)]=data;actual_routes[route]+=1;total+=len(data)
  require((len(recovered),total,dict(actual_routes))==(508,14387684,COUNTS),'Wrong total recovery')
  if args.out:
   require(not args.out.exists(),'Output already exists')
   for (n,name),data in recovered.items():
    f=args.out/f'{n:02d}'/name;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 finally:g.close()
 result={'status':'PASS_EXACT_508_MEMBER_RECOVERY_PLAN' if planned else 'PASS_EXACT_508_MEMBER_RECOVERY','batch':215,'sources':list(range(193,195)),'map_sha256':sha(raw),'helper_sha256':sha(Path(__file__).read_bytes()),'members':508,'bytes':total,'routes':COUNTS,'planned_external_payload':bool(planned),'attribute_equivalent_placed_paths':attribute_equivalent,'attribute_policy':'Differing placed bytes are accepted only when Git clean hashes under the actual repository path agree; exact raw recovery then uses the committed arrival.','canonical_placement_verified':not bool(planned),'supplied_code_executed':False,'checksum_manifest_contents_checked':False,'mode':'verify_only' if args.verify_only else 'reconstruct'}
 if args.result:args.result.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
