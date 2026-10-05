#!/usr/bin/env python3
"""New, read-only intake metadata and three independent displayed polynomial identities."""
import argparse, hashlib, io, json, math, re, subprocess, zipfile
from pathlib import Path
ROOT='/home/codex/.codex/worktrees/2a71/Proofs'
COMMIT='e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9'
HOST='SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/'
SPECS=[('ProveIt_A189281_Borel_Completion.zip','ProveIt_A189281_Borel_Completion',[(101,215),(434,509),(754,789),(870,1088),(1115,1238),(1293,1438)]),('ProveIt_Moving_Gap_Permutations.zip','Moving_Gap_Permutations',[(196,474),(516,629),(1300,1390),(1447,1711),(1746,1914)])]
def sha(b):return hashlib.sha256(b).hexdigest()
def req(v,msg):
 if not v:raise ValueError(msg)
def git(*args):return subprocess.check_output(['git','-C',ROOT,*args])
def read(c,p):return git('show',c+':'+p)
def meta(b):
 d={'bytes':len(b),'sha256':sha(b)}
 try:b.decode();d['lines']=len(b.splitlines())
 except UnicodeDecodeError:pass
 return d
def span(b,a,z,mode):
 lines=b.splitlines(keepends=True);req(1<=a<=z<=len(lines),'read bounds');s=b''.join(lines[a-1:z]);s.decode()
 return {'first_line':a,'last_line':z,'mode':mode,**meta(s)}
def blob(c,p):return {'commit':c,'path':p,'blob':git('rev-parse',c+':'+p).decode().strip(),**meta(read(c,p))}
def norm(a):
 a=list(a)
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(*vs):
 out=[0]*max(map(len,vs))
 for a in vs:
  for i,v in enumerate(a):out[i]+=v
 return norm(out)
def scale(a,c):return norm([c*x for x in a])
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return norm(out)
def shift(a,k):
 out=[0]*len(a)
 for i,v in enumerate(a):
  for j in range(i+1):out[j]+=v*math.comb(i,j)*k**(i-j)
 return norm(out)
def algebra():
 Q=[-5,-54,-5,44,19,2];P=[4,39956,99549,94552,45249,11926,1745,132,4]
 q_check=add(mul([0,-1,1],[60,65,21,2]),[-5,6]);req(Q==q_check,'Q forcing expansion')
 p_check=add(scale(mul([0,2,3,1],shift(Q,4)),2),mul([0,4,1],shift(Q,2)),scale(shift(Q,1),-1),scale(Q,-1));req(P==p_check,'U forcing expansion')
 ell=[[-22,-7],[-2],[3,-1],[-75,-8],[-44,-4],[4]]
 residual=scale(P,-4)
 for k,L in enumerate(ell,1):
  rising=[1]
  for j in range(1,k):rising=mul(rising,[j,1])
  residual=add(residual,mul(mul(L,rising),shift(P,k)))
 req(residual==[0],'V polynomial identity')
 return {'method':'fresh integer polynomial operations on manually transcribed displayed formulas; no delivered program used','Q':Q,'P':P,'Q_identity':True,'U_identity':True,'V_residual':residual,'scope':'Three formal identities only; does not certify analytic continuation, counting recurrence or an all-orders proof.'}
def main():
 parent=git('rev-parse',COMMIT+'^').decode().strip();archives=[]
 for basename,prefix,ranges in SPECS:
  path='docs/incoming/'+basename;b=read(COMMIT,path);z=zipfile.ZipFile(io.BytesIO(b));members=[];allbytes={i.filename:z.read(i) for i in z.infolist() if not i.is_dir()}
  req(len(allbytes)==len([i for i in z.infolist() if not i.is_dir()]),'duplicate member names')
  for i in z.infolist():
   if i.is_dir():continue
   d=allbytes[i.filename];item={'path':i.filename,'crc32':f'{i.CRC:08x}','compressed_bytes':i.compress_size,**meta(d),'coverage':'hash only; no supplied execution'}
   if i.filename.endswith('/README.md') or i.filename.endswith('/SOURCES.md'):
    item['coverage']='full human text read';item['read_spans']=[span(d,1,len(d.splitlines()),item['coverage'])]
   if i.filename.endswith('/article.tex'):
    item['coverage']='selected human text spans; remainder hash-only';item['read_spans']=[span(d,a,e,'selected computation/effectivity and nearby proof interface') for a,e in ranges]
    labs=re.findall(rb'\\label\{([^{}]+)\}',d);refs=sorted(set(s.strip().decode() for group in re.findall(rb'\\(?:[cC]ref|eqref|ref)\*?\{([^{}]+)\}',d) for s in group.split(b',') if s.strip()))
    item['literal_labels']=[s.decode() for s in labs];item['duplicate_labels']=sorted(x.decode() for x in set(labs) if labs.count(x)>1);item['literal_ref_targets']=refs;item['unresolved_literal_refs']=sorted(set(refs)-set(item['literal_labels']))
   members.append(item)
  manifest=prefix+'/SHA256SUMS.txt';checks=[]
  for line in allbytes[manifest].decode().splitlines():
   if not line.strip():continue
   h,name=line.split(None,1);name=name.lstrip('*');candidates=[name,prefix+'/'+name];matches=[x for x in candidates if x in allbytes];req(matches,'manifest member');name=matches[0];req(sha(allbytes[name])==h,'checksum');checks.append({'path':name,'sha256':h})
  req(set(x['path'] for x in checks)==set(allbytes)-{manifest},'checksum coverage')
  archives.append({**blob(COMMIT,path),'absent_in_parent':not git('ls-tree',parent,'--',path),'members':members,'manifest':manifest,'checksums':checks})
 contexts=[]
 source_specs=[('79e7aab60ee856862b36c38cf32cfdb1be95313f',[(3247,3297)]),('d1680cdfa40c44abf0825416b6f36a3e9ec2662c',[(2260,2325)])]
 for c,ranges in source_specs:
  p=HOST+'article.tex';b=read(c,p);req(git('rev-parse',c+':'+p).decode().strip()=='73a53d9784260c2f0d083f2baa62a5535f6d6105','cited article blob')
  contexts.append({**blob(c,p),'read_spans':[span(b,a,z,'selected earlier-source context; no whole prior proof audit') for a,z in ranges]})
 p=HOST+'README.md';c=source_specs[0][0];contexts.append({**blob(c,p),'coverage':'pin only; not human read in this triage'});req(contexts[-1]['blob']=='59ad8b15b9522102e1f6d48f68c1db358a3ac044','cited guide blob')
 p='docs/incoming/README.md';b=read(COMMIT,p);instructions={**blob(COMMIT,p),'read_spans':[span(b,426,442,'standing retention rule')],'destination_note':'The declared SetTheory/Cardinals host has no applicable ancestor AGENTS.md among repository AGENTS paths.'}
 agents=git('ls-tree','-r','--name-only',COMMIT).decode().splitlines();instructions['AGENTS_paths']=[p for p in agents if p=='AGENTS.md' or p.endswith('/AGENTS.md')]
 out={'schema':'bounded-discrete-intake-v1','commit':COMMIT,'parent':parent,'helper_sha256':sha(Path(__file__).read_bytes()),'archives':archives,'source_context':contexts,'instructions':instructions,'fresh_algebra':algebra(),
 'findings':[], 'assessment':{'borel':'Analytic Borel-Laplace summation, not descriptive-set Borel coding. Analytic completion is explicitly distinguished from the integer counting sequence.','moving_gap':'Finite order-dependent coefficient and exact enumeration algorithms; universal means uniform across forest geometries, not Turing universal.','compiler':'No paid ordinary-integer fixed-arity Diophantine compiler or universal simulation supplied in the read interfaces.','inverse':'Eventual rounding on actual sequence values; no explicit effective threshold or cost bound; real special-function evaluation requires an additional representation and accuracy model.'},
 'limits':['Full guides and provenance notes read; only stated manuscript spans read. No full proof, literature/priority or external-source audit.','No delivered scripts/builders, prior collectors or frozen helpers executed/imported, including copied versions.','PDFs, numerical files and saved verification outputs hash-only; delivered test counts and interval tables not independently reproduced.','Fresh three-polynomial identity checks do not prove analytic completion equals exact counts or establish a counting recurrence.'],
 'totals':{'archives':len(archives),'members':sum(len(a['members']) for a in archives),'checksums':sum(len(a['checksums']) for a in archives),'guide_lines':sum(m['lines'] for a in archives for m in a['members'] if m['path'].endswith('/README.md')),'sources_lines':sum(m['lines'] for a in archives for m in a['members'] if m['path'].endswith('/SOURCES.md')),'manuscript_lines_read':sum(e-a+1 for _,_,ranges in SPECS for a,e in ranges),'fresh_polynomial_identities':3},'result':'PASS metadata and three displayed polynomial identities; no concrete defect found in the stated selected interfaces; no full-proof certification'}
 parser=argparse.ArgumentParser();g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');args=parser.parse_args();serial=(json.dumps(out,indent=2,ensure_ascii=False,sort_keys=True)+'\n').encode()
 if args.output:
  with open(args.output,'xb') as f:f.write(serial)
 else:req(Path(args.expect).read_bytes()==serial,'receipt differs')
 print(json.dumps(out['totals'],sort_keys=True));print('PASS')
if __name__=='__main__':main()
