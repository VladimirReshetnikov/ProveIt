#!/usr/bin/env python3
"""Fresh read-only metadata checks for one bounded transseries placement review."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
REV='6132faa30bf6e7674158ad43c9178ab730f560e0'
PARENT='40ad429160b8e756f689f702a28431497f9e9246'
ARRIVAL='516049bf9cf4be8d3240cddb04c9adf453cb65e0'
BASE='Analysis/Transseries/docs/series-and-transseries/'
ACTION=BASE+'Action_Cones_Quartic_Boundaries_Complex_Reversion/'
CUSP=BASE+'Modular_Cusp_Reversion_Stokes_Corrections_q_Gamma/'
GUIDES=['.gitattributes','Analysis/Transseries/README.md',BASE+'README.md']
READS={
 'Analysis/Transseries/AGENTS.md':None,
 'docs/incoming/README.md':[(1,100),(426,439)],
 ACTION+'README.txt':None,
 ACTION+'verification/README.txt':None,
 ACTION+'complex_transseries_reversion.tex':[(66,880),(1780,2041),(2149,2245)],
 CUSP+'README.txt':None,
 CUSP+'SOURCES.txt':None,
 CUSP+'sections/01_scope.tex':None,
 CUSP+'sections/02_reversion.tex':None,
 CUSP+'sections/05_flat.tex':None,
 CUSP+'sections/08_verification_future.tex':None,
}

def require(b,msg):
 if not b:raise RuntimeError(msg)
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args])
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(rev,path):return git('show',rev+':'+path)
def record(rev,path):
 b=blob(rev,path)
 return {'commit':rev,'path':path,'blob':git('rev-parse',rev+':'+path).decode().strip(),'bytes':len(b),'sha256':sha(b)}
def text_record(rev,path):
 r=record(rev,path);b=blob(rev,path);r['lines']=len(b.splitlines());return r

def collect():
 require(git('rev-parse',REV+'^').decode().strip()==PARENT,'parent')
 changed=[]
 for ln in git('diff-tree','--no-commit-id','--name-status','-r',REV).decode().splitlines():
  status,path=ln.split('\t')
  r={'status':status,'path':path}
  if status!='A':r['before']=record(PARENT,path)
  if status!='D':r['after']=record(REV,path)
  changed.append(r)
 require(Counter(r['status'] for r in changed)==Counter({'A':43,'M':3,'D':2}),'changed ledger')
 diffs=[]
 for path in GUIDES:
  b=git('diff','--no-ext-diff','--no-color','--unified=3',PARENT,REV,'--',path)
  diffs.append({'path':path,'before':text_record(PARENT,path),'after':text_record(REV,path),'diff_bytes':len(b),'diff_sha256':sha(b),'diff_lines':len(b.splitlines()),'coverage':'full diff read'})
 spans=[]
 for path,ranges in READS.items():
  r=text_record(REV,path);b=blob(REV,path);lines=b.splitlines(keepends=True)
  if ranges is None:ranges=[(1,len(lines))]
  r['read_spans']=[]
  for first,last in ranges:
   require(1<=first<=last<=len(lines),'read range')
   data=b''.join(lines[first-1:last])
   r['read_spans'].append({'first':first,'last':last,'bytes':len(data),'sha256':sha(data)})
  spans.append(r)
 archives=[]
 for name,wrapper,dest in [
  ('complex_transseries_q_cusps (2).zip','complex_transseries_q_cusps/',CUSP),
  ('complex_transseries_reversion (2).zip','complex_transseries_reversion/',ACTION)]:
  path='docs/incoming/'+name;data=blob(PARENT,path)
  require(blob(ARRIVAL,path)==data,'arrival archive mismatch')
  r=record(PARENT,path);r['arrival']=record(ARRIVAL,path)
  members=[];payload={}
  z=zipfile.ZipFile(io.BytesIO(data))
  for info in z.infolist():
   require(not info.is_dir(),'unexpected directory member')
   require(info.filename.startswith(wrapper),'archive wrapper')
   rel=info.filename[len(wrapper):];b=z.read(info)
   require(rel not in payload,'duplicate archive member');payload[rel]=b
   m={'path':info.filename,'relative_path':rel,'bytes':len(b),'sha256':sha(b)}
   if rel!='MANIFEST.sha256':
    target=dest+rel;require(blob(REV,target)==b,'placement mismatch '+target)
    m['placement']=record(REV,target)
   else:
    m['placement']=None;m['scope']='checksum ledger intentionally omitted from placement, retained in immutable archive'
   members.append(m)
  checks=[]
  for ln in payload['MANIFEST.sha256'].decode().splitlines():
   expected,rel=ln.split(None,1);rel=rel.lstrip('*')
   require(rel in payload and sha(payload[rel])==expected,'manifest mismatch')
   checks.append({'path':rel,'sha256':expected})
  require(set(c['path'] for c in checks)==set(payload)-{'MANIFEST.sha256'},'manifest coverage')
  placed={m['relative_path'] for m in members if m['placement']}
  actual={x['path'][len(dest):] for x in changed if x['status']=='A' and x['path'].startswith(dest)}
  require(actual==placed,'unaccounted destination rows')
  r.update(members=members,manifest_checks=checks,member_count=len(members),placed_count=len(placed))
  archives.append(r)
 # Literal TeX inventories only, not semantic or external-reference certification.
 inventories=[]
 for dest in (ACTION,CUSP):
  paths=[r['path'] for r in changed if r['status']=='A' and r['path'].startswith(dest) and r['path'].endswith('.tex')]
  labels=[];refs=[];bib=[];cites=[]
  for path in paths:
   data=blob(REV,path).decode()
   for i,line in enumerate(data.splitlines(),1):
    line=re.split(r'(?<!\\)%',line)[0]
    for m in re.finditer(r'\\label(?:\[[^]]*\])?\{([^}]+)\}',line):labels.append({'label':m.group(1),'path':path,'line':i})
    for m in re.finditer(r'\\(?:[Cc]ref|eqref|ref|autoref)\*?\{([^}]+)\}',line):
     for key in m.group(1).split(','):refs.append({'label':key.strip(),'path':path,'line':i})
   for m in re.finditer(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',data):bib.append(m.group(1))
   for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',data):cites.extend(k.strip() for k in m.group(1).split(','))
  counts=Counter(r['label'] for r in labels)
  unresolved=[r for r in refs if r['label'] not in counts]
  require(not unresolved,'literal unresolved refs')
  require(not [k for k,v in counts.items() if v>1],'duplicate labels')
  require(set(cites)<=set(bib),'unresolved citations')
  inventories.append({'destination':dest,'tex_files':[text_record(REV,p) for p in paths],'labels':labels,'references':refs,'bibliography_keys':bib,'citation_keys':cites,'unresolved_literal_references':unresolved,'coverage':'literal metadata scan only; does not extend mathematical read spans'})
 # Two exact small mathematical checks, independently reconstructed.
 r=Fraction(1,20)
 Er=3*r**4*(2-r**2)/(1-r**2)**2+4*r**3/(1-r**3)**2+r**6/(1-r**6)
 Tr=3*r*r+Er
 certificate=Er/(3*r*r)+Tr*Tr/(6*r*r*(1-Tr))
 require(Tr<1 and certificate<Fraction(760463,10**7)<Fraction(1,2),'rational disk bound')
 from math import gcd
 walls=[]
 for n in range(1,21):
  pairs={(Fraction(p,q)) for p in range(1,n+1) for q in range(1,n+1)}
  phi=[sum(gcd(k,j)==1 for j in range(1,k+1)) for k in range(1,n+1)]
  require(len(pairs)==2*sum(phi)-1,'wall identity')
  walls.append({'N':n,'walls':len(pairs)})
 return {'schema':'bounded transseries placement review v1','revision':REV,'parent':PARENT,'source_sha256':sha(Path(__file__).read_bytes()),'changed_files':changed,'full_read_diffs':diffs,'read_files':spans,'archives':archives,'tex_metadata':inventories,'fresh_small_math':{'rational_disk_bound':str(certificate),'threshold':str(Fraction(760463,10**7)),'wall_counts':walls},'totals':{'changed_files':len(changed),'archive_members':sum(r['member_count'] for r in archives),'placements':sum(r['placed_count'] for r in archives),'manifest_entries':sum(len(r['manifest_checks']) for r in archives),'full_diff_lines':sum(r['diff_lines'] for r in diffs),'read_spans':sum(len(r['read_spans']) for r in spans),'read_lines':sum(s['last']-s['first']+1 for r in spans for s in r['read_spans'])},'limits':['No supplied, frozen, archived or copied predecessor program executed/imported.','No build, PDF rendering, numerical reproduction, external-source verification or repository mutation.','Label/reference scans and whole-file hashes do not enlarge declared human read scope.','No full analytic proof, historical priority or general ordinary-integer compiler certification.']}

def main():
 p=argparse.ArgumentParser();p.add_argument('--expect',type=Path);p.add_argument('--output',type=Path,default=Path('/tmp/review_transseries_6132faa30.json'));args=p.parse_args()
 result=collect();raw=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
 if args.expect:require(args.expect.read_bytes()==raw,'receipt changed')
 else:args.output.write_bytes(raw)
 print(json.dumps({'status':'PASS','totals':result['totals'],'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
