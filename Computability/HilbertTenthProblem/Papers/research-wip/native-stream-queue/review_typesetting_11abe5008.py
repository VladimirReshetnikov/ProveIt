#!/usr/bin/env python3
"""Pinned, read-only semantic-transfer review of 11abe5008 Parts IV--VI.

verify(repo) reads immutable Git blobs/ZIP members in memory. No archived code
is imported or run. Matching consumes each target occurrence at most once,
separately for each source and kind. This is a textual census, not a TeX parser
or automated proof. Deliberate source-17 deduplications have separate evidence.
"""
from pathlib import Path, PurePosixPath
from fractions import Fraction
import argparse, collections, difflib, hashlib, io, json, re, subprocess, zipfile
SNAPSHOTS = [{'commit': '11abe5008', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex', 'sha256': 'b8b0fee6cf065e1f2cb6e37c8ac0ef595589b8853de107a13b81e1c68418bc27', 'bytes': 503621}, {'commit': '11abe5008', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/README.md', 'sha256': '1ea9b167e8ce3efb9034b42da9f31ace996fa8d376c1265dd5ccf7a276dbc299', 'bytes': 75887}, {'commit': '11abe5008^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex', 'sha256': 'b6c66205f70c3c54406ce0f9dca776181a6e38c5457942155de4eebca92cb469', 'bytes': 256373}, {'commit': '11abe5008^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/README.md', 'sha256': '4b265fb80c99c76adfbc67215c2b656f0e40bbe1d0a394f6ddea5453c2718976', 'bytes': 31730}]
ARCHIVES = [{'case': 'motif', 'arrival': '2a8a39599', 'archive': 'Membrane_Motif_Research_Package.zip', 'sha256': '47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99'}, {'case': 'universal', 'arrival': '2a8a39599', 'archive': 'Universal_Membrane_Research_Package.zip', 'sha256': 'dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5'}, {'case': 'reset', 'arrival': 'aebfa386e', 'archive': 'Reset_Petri_Net_Certificates.zip', 'sha256': 'b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3'}]
REFERENCES = [{'commit': '85294a527', 'path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_membrane_reports_2a8a.md', 'sha256': 'f9617cbd30901f58b588940c2ffb3699fcc2edb033709f6f8ddd8f5841be3885', 'bytes': 16094}, {'commit': '9df1f72ca', 'path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_reset_petri_net_aebfa386e.md', 'sha256': '6173040d7bca9def0f00d16f371256bc9c743dfa83cd687bd97df18aec53dd35', 'bytes': 13011}, {'commit': '653349f6a', 'path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/placement_a7ae02511_inventory.json', 'sha256': 'cec197a4c1367d9dcd671ba85fa242fbdaba5445251794535f0333c2228687cf', 'bytes': 362091}]
REV = '11abe50082d5e031c862a638e7e1b4e649b3d906'
BASE = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/'
CASES = {'motif':('membrane-motif-release/article/membrane_motifs.tex','qoc:mm:'),
 'universal':('literal-membrane-release/article/membrane_frontend.tex','qoc:um:'),
 'reset':('reset-net-release/report/reset-net-certificates.tex','qoc:rn:')}
OLD_SUMMARY = """and source 17's certificates have the form `Σ A² + Σ B·C` and prove more:
their products are strong selector gates, so for natural parameters every
zero over the real nonnegative orthant is natural. Source 15's certificate is"""
NEW_SUMMARY = """and source 17's minimum-duration and trace certificates have the form
`Σ A² + Σ B·C` and prove more: their products are strong selector gates, so
for natural parameters every zero over the real nonnegative orthant is
natural. Source 17's all-duration padding variant is exact only with natural
witnesses; over the nonnegative reals it also admits half-integral padding.
Source 15's certificate is"""

def require(ok,msg):
 if not ok: raise ValueError(msg)
def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def git(repo,*args):return subprocess.run(['git','-C',str(repo),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def blob(repo,rev,p):return git(repo,'show',rev+':'+p)
def pinned(repo,spec):
 b=blob(repo,spec['commit'],spec['path']);require(sha(b)==spec['sha256'] and len(b)==spec['bytes'],'changed Git input '+spec['path']);return b

def norm(t):
 t=re.sub(r'(?<!\\)%[^\n]*','',t)
 t=re.sub(r'\\label(?:\[[^]]+\])?\{[^}]+\}','',t)
 t=re.sub(r'qoc:(?:mm|um|rn):','',t)
 t=re.sub(r'(\\cite(?:\[[^]]*\])?\{)([^}]*)(\})',lambda m:m[1]+','.join(re.sub(r'^(?:mm:|um:|rn:)','',k) for k in m[2].split(','))+m[3],t)
 t=t.replace(r'\mmzero',r'\zero').replace(r'\rnind',r'\ind').replace(r'\rncode',r'\code')
 t=re.sub(r'\\(?:notag|nonumber|displaystyle|textstyle)\b','',t)
 return re.sub(r'\s+','',t)
def labels(t):return re.findall(r'\\label(?:\[[^]]+\])?\{([^}]+)\}',t)
def spans(t,case):
 if case=='motif':
  a=t.index(r'\part{Exact spatially');b=t.index(r'\part{Literal universal');c=t.index(r'\section{A compact implementation contract}');d=t.index(r'\section{Artifact map and representation conventions}')
 elif case=='universal':
  a=t.index(r'\part{Literal universal');b=t.index(r'\part{Reset Petri');c=t.index(r'\section{Artifact map and representation conventions}');d=t.index(r'\section{Source notation and the program export}')
 else:
  a=t.index(r'\part{Reset Petri');b=t.index(r'\appendix',a);c=t.index(r'\section{Source notation and the program export}');d=t.index(r'\begin{thebibliography}',c)
 return [(a,b),(c,d)]
def blocks(t,kind):
 types={'display':('equation','equation*','align','align*','gather','gather*'),
  'formal':('theorem','lemma','proposition','corollary','definition','remark','example','question'),
  'proof':('proof',),'table':('tabular','longtable'),'listing':('lstlisting',),
  'abstract':('abstract',),'diagram':('tikzpicture',)}[kind]
 out=[]
 for typ in types:
  p=r'\\begin\{'+re.escape(typ)+r'\}(.*?)\\end\{'+re.escape(typ)+r'\}'
  for m in re.finditer(p,t,re.S):out.append(dict(env=typ,offset=m.start(),line=t.count('\n',0,m.start())+1,body=m[1]))
 if kind=='display':
  for m in re.finditer(r'(?<!\\)\\\[(.*?)\\\]',t,re.S):out.append(dict(env='bracket',offset=m.start(),line=t.count('\n',0,m.start())+1,body=m[1]))
 return sorted(out,key=lambda d:d['offset'])
def compare(old,new,case,prefix):
 ranges=spans(new,case);scoped='\n'.join(new[a:b] for a,b in ranges)
 oldlabels=labels(old);newlabels=labels(scoped)
 require(len(newlabels)==len(set(newlabels)),'duplicate scoped target label')
 require(all(newlabels.count(prefix+l)==1 for l in oldlabels),'label missing or duplicated')
 result={'original_labels':len(oldlabels),'original_labels_all_preserved':True,'kinds':{}}
 missing={}
 for kind in ('display','formal','proof','table','listing','abstract','diagram'):
  source=blocks(old,kind);target=[b for b in blocks(new,kind) if any(a<=b['offset']<z for a,z in ranges)]
  available=collections.defaultdict(collections.deque)
  for i,b in enumerate(target):available[(b['env'],norm(b['body']))].append(i)
  maps=[];miss=[]
  for i,b in enumerate(source):
   key=(b['env'],norm(b['body']));item=dict(source_index=i,source_line=b['line'],environment=b['env'],normalized_sha256=sha(key[1]))
   if available[key]:
    j=available[key].popleft();item.update(target_index=j,target_line=target[j]['line']);maps.append(item)
   else:item['body']=b['body'];miss.append(item)
  require(len({m['target_index'] for m in maps})==len(maps),'target occurrence reused')
  result['kinds'][kind]={'original':len(source),'preserved':len(maps),'occurrences':maps}
  missing[kind]=miss
 if case!='reset':require(not any(missing.values()),case+' original block changed')
 else:
  require({k:len(v) for k,v in missing.items() if v}=={'display':3,'proof':2,'table':2},'unexpected reset omissions')
  expected_displays={norm(x) for x in [r'A=n-j,\qquad B_c=pj.',r'(3p+1)n+2.',r'A=n-pj-s,\qquad B_c=j,\qquad0\leq s<p.']}
  require({norm(x['body']) for x in missing['display']}==expected_displays,'changed omitted prime formulas')
  require('After $k$ completed pair loops' in missing['proof'][0]['body'],'wrong omitted macro proof')
  require('At a zero the gates select exactly one branch' in missing['proof'][1]['body'],'wrong omitted source-fiber proof')
  result['declared_deduplications']={k:v for k,v in missing.items() if v}
 # Mathematical macro definitions, including renamed clashes. File rendering is not mathematics.
 def defs(t):return {name:body for name,body in re.findall(r'\\newcommand\{(\\\w+)\}([^\n]*)',t)}
 targetdefs=defs(new);md=[]
 for name,body in defs(old).items():
  if name==r'\file':continue
  dest={'motif':{r'\zero':r'\mmzero'},'universal':{},'reset':{r'\ind':r'\rnind',r'\code':r'\rncode'}}[case].get(name,name)
  require(norm(body)==norm(targetdefs[dest]),'changed macro '+name);md.append({'source':name,'target':dest})
 result['macro_definitions']=md
 return result

def table_cells(body):
 # Reviewed state table has six cells in each data row. Strip only its literal typography.
 out={}
 for line in body.splitlines():
  if '&' not in line:continue
  line=line.replace(r'\mathrm','').replace('$','').replace('(','').replace(')','').replace(',','').replace(r'\\','')
  cols=[re.sub(r'\s+','',c) for c in line.split('&')]
  if not re.fullmatch('[A-O]',cols[0]):continue
  for i in (0,3):
   if i>=len(cols) or not cols[i]:continue
   require(re.fullmatch('[A-O]',cols[i]) is not None,'bad state')
   for bit,v in enumerate(cols[i+1:i+3]):
    v=v.split('\\')[0];out[cols[i]+str(bit)]=None if v in ('halt','undefined') else v
 require(len(out)==30,'not complete binary table');return out

def dedup_evidence(old,full,archives):
 universal='\n'.join(full[a:b] for a,b in spans(full,'universal'));reset='\n'.join(full[a:b] for a,b in spans(full,'reset'))
 oldtables=blocks(old,'table');newtables=blocks(universal,'table')
 tmold=next(x['body'] for x in oldtables if '$0RB$' in x['body']);tmnew=next(x['body'] for x in newtables if r'$(0,R,\mathrm B)$' in x['body'])
 require(table_cells(tmold)==table_cells(tmnew),'deduplicated TM table differs')
 costsold=next(x['body'] for x in oldtables if 'Case & ADDs & positive SUBs' in x['body'])
 costsnew=next(x['body'] for x in newtables if 'Positive' in x['body'] or ('SUB' in x['body'] and '2pN' in x['body']))
 # Division rows agree after n->N and s->r; column headings differ.
 rows=[]
 for l in costsold.splitlines():
  if '$s' not in l:continue
  l=l.replace('s','r').replace('n','N').replace(r'\bottomrule','')
  row=norm(l).replace('$',''); newrow=norm(costsnew).replace('$','').replace(r'\SUB,','')
  require(row in newrow,'prime division cost row changed');rows.append(row)
 # Source-16 all-natural invariant proof covers the omitted source-17 macro proof.
 needed=[r'X=2(Q-k)+r',r'K=k',r'Y=Y_0-k',r'K=2k',r'Y+K=2Y_0',
         r'5Q+r+2',r'7Y_0+2+w',r'5Q+r+7Y_0+w+4',
         r'A=N-k',r'B=pk',r'A=N-pk-j',r'B=k',r'0\leq j<p',r'(3p+1)N+2']
 un=norm(universal)
 for s in needed:require(norm(s) in un,'missing retained all-input invariant '+s)
 for label in ('lem:virtual','thm:poly','lem:prime','tab:cost','tab:tm'):
  require(('qoc:um:'+label) in reset,'missing explicit dedup pointer '+label)
 # The source-16 theorem and proof are occurrence-preserved separately by compare.
 for s in ['nonnegative-real zero fiber is exactly its natural zero fiber','Since the halt code is not a branch source','Starting with natural counters']:
  require(s in universal,'lost strong-gate or first-halt hypothesis')
 u=archives['universal'];r=archives['reset'];ur='literal-membrane-release/';rr='reset-net-release/'
 pairs=[('source/virtual3.json','direct/virtual3.json'),('source/virtual3.txt','direct/virtual3.txt'),
 ('two-counter/source/virtual3.json','packet/virtual3.json'),('two-counter/source/virtual3.txt','packet/virtual3.txt'),
 ('two-counter/source/literal2.json','packet/literal2.json'),('two-counter/source/literal2.txt','packet/literal2.txt')]
 same=[]
 for a,b in pairs:
  require(r[rr+a]==u[ur+b],'deduplicated program file differs');same.append(dict(reset=a,universal=b,sha256=sha(r[rr+a])))
 x=r[rr+'source_quadratic.py'].decode();y=u[ur+'direct/quadratic_core.py'].decode()
 changes=[(x[i:j],y[k:l]) for tag,i,j,k,l in difflib.SequenceMatcher(None,x,y,autojunk=False).get_opcodes() if tag!='equal']
 require(x.replace('Not an arbitrary reset-trace verifier','Not an arbitrary membrane-trace verifier')==y,'unexpected compiler difference')
 require(x.count('Not an arbitrary reset-trace verifier')==1,'compiler replacement ambiguous')
 changes=[('reset-trace','membrane-trace')]
 # The manuscripts describe proof-note overlap informally as word 8-grams.
 # Pin both notes, and report reproducible ASCII-word occurrence coverage (the rounded 91%/98%).
 overlaps=[]
 for a,b in [('source/SOURCE_REGISTER_PROOF.md','direct/PROOF.md'),('two-counter/source/PROOF.md','packet/PROOF.md')]:
  aa=re.findall(r'\b\w+\b',r[rr+a].decode().lower());bb=re.findall(r'\b\w+\b',u[ur+b].decode().lower());pool={tuple(bb[i:i+8]) for i in range(len(bb)-7)}
  hits=sum(tuple(aa[i:i+8]) in pool for i in range(len(aa)-7))
  rounded=(200*hits+len(aa)-7)//(2*(len(aa)-7)); require(rounded==[91,98][len(overlaps)],'reported overlap percentage changed')
  overlaps.append(dict(reset=a,universal=b,source_sha256=sha(r[rr+a]),target_sha256=sha(u[ur+b]),source_8grams=len(aa)-7,matching_8grams=hits,rounded_percent=rounded))
 return {'tm_entries':30,'undefined_entry':'J1','prime_division_cost_rows':rows,'retained_invariants':needed,
  'scope':'all natural half tapes and every positive raw prime-coded input, with scratch-zero cut and cofactor conventions retained',
  'identical_program_files':same,'compiler_text_edits':changes,'proof_note_overlap':overlaps}

def padding_fixture():
 h,H,B,v=328,11,6,14;nmin=h+3*H-B+2*v+5;require(nmin==388,'minimum changed')
 N=nmin+1;z=Fraction(1,2);residual=N-h-3*H+B-2*v-5-2*z;require(residual==0,'half-integral padding failed')
 require((N-nmin)%2==1,'not parity obstruction')
 return dict(h=h,H=H,B=B,v_h=v,N_min=nmin,N=N,z=str(z),padding_residual=str(residual),
  scope='exact padding residual extension of the already proved natural source/peak witness; no large source trace is replayed here')

def correction(readme,article):
 require(readme.count(OLD_SUMMARY)==1,'README correction context changed')
 fixed_readme=readme.replace(OLD_SUMMARY,NEW_SUMMARY)
 require(fixed_readme.count('one docstring word')==2,'README metadata wording changed')
 fixed_readme=fixed_readme.replace('one docstring word','one word in the emitted scope metadata')
 require(article.count('one word of a docstring')==1,'article metadata wording changed')
 fixed_article=article.replace('one word of a docstring','one word in the emitted scope metadata')
 patches=[];files=[]
 for path,old,new in [('README.md',readme,fixed_readme),('article.tex',article,fixed_article)]:
  patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+BASE+path,tofile='b/'+BASE+path))
  # Exact hunk replay independent of string replacements.
  oldlines=old.splitlines(True);out=[];at=0;chunks=patch.splitlines(True);i=2
  while i<len(chunks):
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',chunks[i]);require(m is not None,'bad hunk');start=int(m[1])-1
   out.extend(oldlines[at:start]);at=start;i+=1
   while i<len(chunks) and not chunks[i].startswith('@@'):
    line=chunks[i];tag=line[0];content=line[1:]
    if tag in (' ','-'):require(oldlines[at]==content,'patch old context mismatch');at+=1
    if tag in (' ','+'):out.append(content)
    i+=1
  out.extend(oldlines[at:]);require(''.join(out)==new,'patch does not reproduce replacement')
  files.append(dict(target=BASE+path,before_sha256=sha(old),after_sha256=sha(new)))
  patches.append(patch)
 patch=''.join(patches)
 return dict(files=files,patch_sha256=sha(patch),private_hunk_replay=True,pdf_changed=False),patch

def verify(repo):
 require(isinstance(repo,(str,Path)),'repository path required');repo=Path(repo)
 snaps=[pinned(repo,s) for s in SNAPSHOTS];full=snaps[0].decode();readme=snaps[1].decode()
 refs=[pinned(repo,s) for s in REFERENCES];placement=json.loads(refs[2])
 archives={};manifest=[];placed_paths=set();placed_coverage=0
 for spec in ARCHIVES:
  data=blob(repo,spec['arrival'],'docs/incoming/'+spec['archive']);require(sha(data)==spec['sha256'],'archive pin changed')
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   members={}
   for zi in z.infolist():
    if zi.is_dir():continue
    p=PurePosixPath(zi.filename);require(not p.is_absolute() and '..' not in p.parts and '\\' not in zi.filename,'unsafe ZIP path')
    require(zi.filename not in members and (zi.external_attr>>16)&0o170000!=0o120000,'duplicate/symlink ZIP member')
    members[zi.filename]=z.read(zi)
  archives[spec['case']]=members
  pa=next(a for a in placement['archives'] if a['path']=='docs/incoming/'+spec['archive']);require(pa['sha256']==spec['sha256'],'placement archive differs')
  pm={m['member']:m for m in pa['members']};require(set(pm)==set(members),'placement inventory member mismatch')
  mm=[]
  for name,b in sorted(members.items()):
   m=pm[name];require(sha(b)==m['sha256'] and len(b)==m['bytes'],'placement member pin differs')
   for p in m['placed_paths']:
    require(blob(repo,REV,p)==b,'typeset commit modified original companion '+p);placed_paths.add(p)
   placed_coverage+=bool(m['placed_paths']);mm.append(dict(path=name,bytes=len(b),sha256=sha(b),placed_paths=m['placed_paths']))
  manifest.append(dict(**spec,bytes=len(data),members=mm))
 census={}
 for case,(member,prefix) in CASES.items():census[case]=compare(archives[case][member].decode(),full,case,prefix)
 dedup=dedup_evidence(archives['reset'][CASES['reset'][0]].decode(),full,archives)
 patchmeta,patch=correction(readme,full)
 for marker in [r'\bigl(N-h-3H+B-2v_h-5-2z\bigr)^2',r'N=389,z=1/2',r'This variant is \emph{not} real-exact.']:
  require(marker in full,'preserved all-duration warning changed')
 summary={kind:{k:sum(c['kinds'][kind][k] for c in census.values()) for k in ('original','preserved')} for kind in next(iter(census.values()))['kinds']}
 result={'status':'PASS_WITH_TWO_EDITORIAL_CORRECTIONS','revision':REV,'snapshots':SNAPSHOTS,'references':REFERENCES,
  'archives':manifest,'counts':{'archives':len(manifest),'archive_members':sum(len(m) for m in archives.values()),
   'unchanged_placed_companion_paths':len(placed_paths),'original_members_covered_by_placed_companions':placed_coverage,
   'labels':sum(c['original_labels'] for c in census.values()),'blocks':summary},'occurrence_census':census,
  'intentional_deduplication_evidence':dedup,'padding_counterexample':padding_fixture(),'correction':patchmeta,
  'limits':['no archived program imported/executed','no unchanged author suite rerun','no historical Parts I--III full review',
   'no PDF layout or future-commit audit','text normalization is not a TeX parser or proof assistant',
   'source-17 explicit deduplication is semantic reuse, not exact transcription',
   'external schemas/horizons still determine arity; no fixed-arity universal operation improvement']}
 return result,patch

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--write',type=Path);p.add_argument('--expect',type=Path);p.add_argument('--patch',type=Path);a=p.parse_args()
 result,patch=verify(a.repo);result['checker_sha256']=sha(Path(__file__).read_bytes())
 result=json.loads(json.dumps(result));data=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if a.expect:require(exact(result,json.loads(a.expect.read_text())),'saved receipt mismatch')
 if a.write:a.write.write_text(data)
 if a.patch:a.patch.write_text(patch)
 print(json.dumps({'status':result['status'],'counts':result['counts'],'correction':result['correction']},sort_keys=True))
if __name__=='__main__':main()
