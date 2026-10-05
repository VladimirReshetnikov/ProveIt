#!/usr/bin/env python3
"""Fresh immutable metadata only. Never imports or runs source/archive programs."""
import argparse,collections,hashlib,io,json,pathlib,re,stat,subprocess,zipfile
REV='a21a42d8c27f62ac3443393f88adfeb3d5f6f265'
ARR='d7cf7d5547a50a6cf372f2cfaad96e950a68c03a'
CONTEXT='45cb4552af638a55dc555e98bae284950c13befb'
HOST='Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
ZIP='docs/incoming/Beyond_Ord_Research_Package.zip'
REPO=None
SPANS=[[1297,1401],[2600,2685],[58835,58898],[58906,58944],[59198,59236],[59590,59690],[59702,59748],[59800,60185],[60892,61282],[61640,61860],[62011,62140],[71092,71180]]
PLACEMENTS={'36-horizons-SOURCE_AUDIT.txt':'SOURCE_AUDIT.txt','code/36-horizons-build.sh':'build.sh','code/36-horizons-notation_demo.py':'code/notation_demo.py','data/36-horizons-DOCUMENT_CHECKS.json':'DOCUMENT_CHECKS.json','data/36-horizons-verification.json':'code/verification.json'}
def ck(v,m):
 if not v:raise RuntimeError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(REPO),*args])
def obj(rev,path):
 b=git('show',rev+':'+path);return b,{'commit':rev,'path':path,'blob':git('rev-parse',rev+':'+path).decode().strip(),'bytes':len(b),'sha256':sha(b)}
def spans(b,ss):
 ls=b.splitlines(keepends=True);out=[]
 for x,y in ss:
  ck(1<=x<=y<=len(ls),'span range');z=b''.join(ls[x-1:y]);out.append({'first':x,'last':y,'lines':y-x+1,'bytes':len(z),'sha256':sha(z)})
 return out
def labels(b):
 t=b.decode();return [(m.group(1),t.count('\n',0,m.start())+1) for m in re.finditer(r'\\label(?:\[[^\]]*\])?\s*\{([^{}]+)\}',t)]
def main():
 global REPO
 a=argparse.ArgumentParser();a.add_argument('--repo',type=pathlib.Path,required=True);a.add_argument('--output');a.add_argument('--expect');args=a.parse_args();REPO=args.repo
 parent=git('rev-parse',REV+'^').decode().strip();changed=git('diff','--name-only',parent,REV).decode().splitlines();ck(changed==[HOST+'/'+x for x in ['README.md','article.pdf','article.tex']],'changed paths')
 files=[];bs={}
 for f in ['README.md','article.tex','article.pdf']:
  b,m=obj(REV,HOST+'/'+f);old,om=obj(parent,HOST+'/'+f);bs[f]=b;bs['old_'+f]=old
  rec={'after':m,'before':om,'coverage':'PDF bytes only' if f.endswith('pdf') else 'selected source spans' if f.endswith('tex') else 'full changed-text diff'}
  if f!='article.pdf':
   d=git('diff','--no-ext-diff','--unified=3',parent,REV,'--',HOST+'/'+f)
   rec['diff']={'sha256':sha(d),'bytes':len(d),'lines':len(d.splitlines()),'fully_read':f=='README.md'}
  if f=='article.tex':rec['read_spans']=spans(b,SPANS)
  files.append(rec)
 arch,am=obj(ARR,ZIP);z=zipfile.ZipFile(io.BytesIO(arch));ck(z.testzip() is None,'zip CRC');names=z.namelist();ck(len(names)==len(set(names))==9,'members');members=[];data={}
 for info in z.infolist():
  p=pathlib.PurePosixPath(info.filename);ck(not p.is_absolute() and '..' not in p.parts and not info.is_dir() and not stat.S_ISLNK(info.external_attr>>16) and not info.flag_bits&1,'unsafe member');b=z.read(info);data[info.filename]=b;members.append({'path':info.filename,'bytes':len(b),'compressed_bytes':info.compress_size,'crc32':format(info.CRC,'08x'),'sha256':sha(b),'git_content_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'coverage':'metadata authentication only this review'})
 manifest=json.loads(data['Beyond_Ord/DOCUMENT_CHECKS.json']);matches=[]
 def walk(v):
  if isinstance(v,dict):
   for k,x in v.items():
    if isinstance(x,str) and re.fullmatch('[a-f0-9]{64}',x):matches.append((k,x))
    else:walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 walk(manifest);ck(len(matches)==4,'document hashes')
 for k,h in matches:ck(sha(data['Beyond_Ord/'+k])==h,'manifest mismatch')
 placed=[]
 for p,m in PLACEMENTS.items():
  b,r=obj(REV,HOST+'/'+p);old,ro=obj('6571ee1afb1984a21aeddd84275c3a7cc2a28e80',HOST+'/'+p);ck(b==old==data['Beyond_Ord/'+m],'placement bytes');r.update({'member':'Beyond_Ord/'+m,'placement_commit':ro['commit'],'unchanged_since_placement':True});placed.append(r)
 sl=labels(data['Beyond_Ord/beyond_ord.tex']);hl=labels(bs['article.tex']);ol=labels(bs['old_article.tex']);hc=collections.Counter(x for x,l in hl);oc=collections.Counter(x for x,l in ol)
 ck(len(sl)==70 and len(set(x for x,l in sl))==70,'source labels');ck(len(hl)==2293 and len(hc)==2293,'host labels');ck(len(ol)==2188 and len(oc)==2188,'parent labels');ck(set(oc)<=set(hc),'lost labels')
 routes=[]
 for lab,line in sl:
  target='swo:hn:'+lab;ck(hc[target]==1,'route');routes.append({'source_label':lab,'source_line':line,'host_label':target,'host_line':next(l for x,l in hl if x==target)})
 text=bs['article.tex'].decode();refs=[]
 for pat in [r'\\(?:[cC]ref|ref|eqref|pageref|autoref)\*?(?:\[[^\]]*\])?\{([^{}]+)\}',r'\\hyperref\[([^\]]+)\]']:
  for m in re.finditer(pat,text):
   for x in m.group(1).split(','):refs.append(x.strip())
 missing=sorted(set(refs)-set(hc));ck(not missing,'unresolved literal reference')
 bib=re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',text);cites=[]
 for m in re.finditer(r'\\cite\w*\*?(?:\[[^\]]*\]){0,2}\{([^{}]+)\}',text):cites.extend(x.strip() for x in m.group(1).split(','))
 ck(not set(cites)-set(bib),'unresolved citation');ck(len(bib)==len(set(bib)),'duplicate bibliography')
 env=collections.Counter(re.findall(r'\\begin\{(theorem|proposition|definition|lemma|corollary|question)\}',data['Beyond_Ord/beyond_ord.tex'].decode()))
 ck(sum(v for k,v in env.items() if k!='question')==42 and env['question']==10,'source statements')
 cross=text[text.index('\\label{swo:xvii:app:crosswalk}'):text.index('% ---- hand chunk bibliography',text.index('\\label{swo:xvii:app:crosswalk}'))]
 ck(len(re.findall(r'\\Cref\{swo:hn:[^}]+\}',cross))==52,'crosswalk entries')
 inherited=[]
 for n in ['review_beyond_ord_package_d7cf7d554.md','review_beyond_ord_horizons_placement_6571ee1af.md','review_beyond_ord_gb_62b16914e.md','review_beyond_ord_write_62b16914e.md']:
  b,m=obj(CONTEXT,WIP+'/'+n);m['coverage']='full bounded-review note read; inherited scope only';inherited.append(m)
 instr=[]
 for p,ss in [('Algebra/SurrealNumbers/AGENTS.md',None),('docs/incoming/README.md',[[426,439]])]:
  b,m=obj(REV,p);m['read_spans']=spans(b,ss or [[1,len(b.splitlines())]]);instr.append(m)
 result={'status':'SCOPED_PUBLICATION_REVIEW_WITH_EDITORIAL_FINDINGS','helper_sha256':sha(pathlib.Path(__file__).read_bytes()),'commit':REV,'parent':parent,'context_commit':CONTEXT,'changed_paths':changed,'files':files,'archive':dict(am,members=members,recorded_hashes_checked=matches),'placements':placed,'source36_routes':routes,'source36_environment_counts':dict(env),'crosswalk_entries':52,'labels':{'parent':len(ol),'new':len(hl),'added':sorted(set(hc)-set(oc)),'removed':[],'all_original70_once':True,'new_prefix_counts':{p:sum(x.startswith(p) for x in set(hc)-set(oc)) for p in ['swo:hn:','swo:xvii:','swo:part:horizons']},'part_declarations_before':len(re.findall(r'\\part\{',bs['old_article.tex'].decode())),'part_declarations_after':len(re.findall(r'\\part\{',text)),'reference_occurrences':len(refs),'unique_reference_targets':len(set(refs)),'missing_reference_targets':missing,'bibliography_entries':len(bib),'citation_occurrences':len(cites)},'inherited_reviews':inherited,'instructions':instr,'coverage_limits':['No full article diff/body proof audit','No PDF render/page certification','No archived or predecessor program import/execution','Label routes are locators, not whole-body equivalence or rendered-number proof','External references not verified; no external-literature theorem certified','Part XVI corrections independently reviewed by Pascal in a separate note'],'read_counts':{'article_lines':sum(y-x+1 for x,y in SPANS),'guide_diff_lines':files[0]['diff']['lines'],'archive_members':9,'placed_files':5,'placed_bytes':sum(x['bytes'] for x in placed)}}
 payload=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if args.expect:ck(payload==pathlib.Path(args.expect).read_bytes(),'exact receipt')
 if args.output:
  with open(args.output,'xb') as f:f.write(payload)
 print(json.dumps(result['read_counts'],sort_keys=True));print(json.dumps({k:v for k,v in result['labels'].items() if k not in ['added']},sort_keys=True))
if __name__=='__main__':main()
