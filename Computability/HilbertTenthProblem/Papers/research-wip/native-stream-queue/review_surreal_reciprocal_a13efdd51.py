#!/usr/bin/env python3
"""Pinned reciprocal-note preservation audit. Standard-library Python, read-only
Git, and pdfinfo only; executes neither author programs nor TeX builds.
The mathematical reading is recorded separately in the companion note.
"""
import argparse,collections,difflib,hashlib,json,posixpath,re,subprocess,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('This audit must run without -O')
PARENT='acb0041e13eb423320c0a598fe9626093de0a222'
COMMIT='a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af'
REPORTS={'found': 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations',
 'hset': 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets',
 'lwo': 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals',
 'rvs': 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure'}
SWO='Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders'
PINS={('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/AGENTS.md'): 'ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md'): '216ed18c42c26177c7e8338aba012d5b67f54ac02483efa024c12b0e6a599761',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.pdf'): '66bec6d5dcd8e5fd3a6b174b3d6afb870892fdcf5668899d2ea7280c197e199d',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex'): 'e4e5d5645485d2f142fd206e929e024cbc0cb069532aec8217c803fc27a438a6',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/README.md'): '45d0c24e98af7ad14f9175874d30aa8fd394fad5d96366425f1e8a1797ea5c35',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.pdf'): 'd4b020bbd5a5744599f0f5b141372ca9b6e5eab0a9658f2308c33f454d19b5ed',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.tex'): '73a66332714e831576e6b3fd8bed0361f939a25b34f4d49954aff5a00e1c59f1',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md'): '8fc8b16c54a45cab946f383ee47b9f87b31b105939e0d65f681c88a1f1a6a568',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.pdf'): '4b228811c4719c063aad1932d540e7f0e531ff6a1ca082df014a6fce0d7a2cbf',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.tex'): '728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/README.md'): 'b93a43a9df4411b8bb6de212d71269a2c6e11a4878fb559c1b8d86d5007fa74f',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.pdf'): '9fa1d1fa906a20a2fe12d2efeccc15cc21d4bb5c0df17a2f5610fca660f699a0',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.tex'): '48bba00c76598e56cc64ad20085df7e79dded0bb73d17f39e9fa037096f5faae',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/README.md'): '36c83cb2674b3f0adfae8cd0a9d46af4845ab829f701fe15aa0a3d7ab908206a',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.pdf'): '6c2515cc92dd60e9fc9a2944d6c7ad9c5fd6c361657e80a7ce6ed63f79ec9346',
 ('a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.tex'): '8ae6055f08dcd07ad62b82267cdd8ea5491318214b17177c239201ed220d83f7',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md'): 'dea99112a80a7bcd0970f8a1b21ac9115a5bf1bf3d7bf35166c9b786781d0dd9',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.pdf'): 'd5313b5fc90b147d67117f384d08d9b204e75229234657134927779fdd847125',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex'): '8997a7a1b1d60358fe9c2ea959789c3ed53724c848c708813e8d17b46a204d78',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/README.md'): 'd4bf2d26fe2f32c8c7b7d61dd843fbd38e5c440d2b58bce11221e95698cb3a97',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.pdf'): 'f9aa9a74c1a0a4addefa1f02a6380f2f547a413752cc99bf44e0032cd9cef3e7',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.tex'): 'c8a8af019f105b07c500b8aa409e429df5f2193f607069bdbfb8b4be63ac1b9e',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/README.md'): '82844173fa6eea4e93a1bd68af09b83011e414c72c3f12e4aa9f628dab38f493',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.pdf'): 'c4955f0da7ee362360c9397971e51b83d9e95091fe4c9583c87d6deb83b1b1ad',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.tex'): '529f423114a555127f8096888572eeb01171576c3b9d2ea96f141f8725d0512b',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/README.md'): '8c2a12dac2892f685359a3b56ffa5fd9f1b23e3a181d0cd373a785e787716a56',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.pdf'): '35a16467ebc1005a13627d388e6af0bf8355d41482b15de916b4be83a3c0d5d9',
 ('acb0041e13eb423320c0a598fe9626093de0a222', 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.tex'): 'ddc2c4d5e407b9fa866321aff8f541a54021964c9805216642cf51035d696e34'}
FORMAL=('theorem','lemma','proposition','corollary','definition','example','question','remark','note','principle','observation','claim','conjecture','problem','convention','warning')
DISPLAY=('equation','equation*','align','align*','gather','gather*','multline','multline*','displaymath','eqnarray','eqnarray*','flalign','flalign*','alignat','alignat*')
EXTERNAL_NUMBERS={'swo:sw:stageeta':'7.2','swo:sk:prop:cutoffeta':'7.4','swo:sw:permutationeta':'12.1','swo:cf:choice':'13.1','swo:rem:answered-choice':'13.4','swo:st:thm:transition':'8.3','swo:st:n10.5':'8.5','swo:n16.3':'27.3'}
LWO_NUMBERS={'lwo:lem:prefix-free':'4.1','lwo:prop:cardinality':'4.4','lwo:lem:cut-code':'5.1','lwo:thm:cube-strict':'5.3','lwo:lem:eventual':'6.1','lwo:thm:no-long':'6.2','lwo:thm:ordinal-spectrum':'6.4','lwo:lem:all-small-cubes':'8.1','lwo:thm:full-length':'8.2','lwo:lem:extrema':'11.1','lwo:thm:adjacency':'11.2','lwo:thm:blocks':'11.5','lwo:sp:thm:universality':'15.1'}
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def git(repo,*a):return subprocess.check_output(['git','-C',str(repo),*a],timeout=60)
def blob(repo,c,p):return git(repo,'show',c+':'+p)
def pinned(repo,c,p):
 b=blob(repo,c,p);need(sha(b)==PINS[(c,p)],'source byte mismatch: '+p);return b
def uncomment(t):return re.sub(r'(?<!\\)%[^\n]*','',t)
def label_list(t):return re.findall(r'\\label(?:\[[^\]]*\])?\{([^}]+)\}',uncomment(t))
def blocks(t,environments):
 # Byte-exact full bodies; balanced environment nesting also handles proof
 # containers that contain enumerate/align or another theorem environment.
 tokens=list(re.finditer(r'\\(begin|end)\{([^}]+)\}',t));stack=[];out=[]
 for m in tokens:
  if m[1]=='begin':stack.append((m[2],m.start()))
  else:
   need(stack and stack[-1][0]==m[2],'unbalanced environment '+m[2]);env,start=stack.pop()
   if env in environments:out.append((start,m.end(),env,t[start:m.end()]))
 need(not stack,'unclosed environments')
 return sorted(out)
def displays(t):
 a=blocks(t,DISPLAY)
 for m in re.finditer(r'(?<!\\)\\\[.*?(?<!\\)\\\]',t,re.S):a.append((m.start(),m.end(),'bracket',m[0]))
 for m in re.finditer(r'(?<!\\)\$\$.*?(?<!\\)\$\$',t,re.S):a.append((m.start(),m.end(),'dollar',m[0]))
 return sorted(a)
def number_map(t):
 # Pinned SWO/LWO use theorem[section] with every listed environment sharing
 # theorem's alias counter. Count actual section/theorem begin events, then
 # associate all labels inside that formal body. No compiled .aux is assumed.
 t=uncomment(t);section=counter=0;out={}
 events=r'\\section(\*)?\{|\\begin\{('+'|'.join(FORMAL)+r')\}'
 fs={a:(b,env,body) for a,b,env,body in blocks(t,FORMAL)}
 for m in re.finditer(events,t):
  if m[0].startswith('\\section'):
   if m[1] is None:section+=1;counter=0
  else:
   counter+=1
   for lab in label_list(fs[m.start()][2]):out[lab]=f'{section}.{counter}'
 return out

def heading_numbers(t):
 counters=[0,0,0];out={}
 for m in re.finditer(r'\\(section|subsection|subsubsection)(\*)?\{([^\n]*)',uncomment(t)):
  if m[2]:continue
  depth=['section','subsection','subsubsection'].index(m[1]);counters[depth]+=1
  for z in range(depth+1,3):counters[z]=0
  out['.'.join(map(str,counters[:depth+1]))]=m[3].rstrip('}')
 return out

def inventory(repo,c,d):
 raw=git(repo,'ls-tree','-r','--full-tree','-z',c,'--',d)
 out={}
 for line in raw.split(b'\0'):
  if not line:continue
  fields,p=line.split(b'\t',1);mode,kind,oid=fields.decode().split();p=p.decode()
  need(kind=='blob' and mode=='100644','unexpected report entry '+p)
  b=blob(repo,c,p);out[p]={'bytes':len(b),'sha256':sha(b),'git_blob':oid}
 return out

def pdf_summary(b,where):
 p=Path(where)/'check.pdf';p.write_bytes(b)
 info=subprocess.check_output(['pdfinfo',str(p)],text=True,timeout=60)
 pages=int(re.search(r'^Pages:\s+(\d+)$',info,re.M)[1]);encrypted=re.search(r'^Encrypted:\s+(.*)$',info,re.M)[1].strip()
 need(b.startswith(b'%PDF-') and b'%%EOF' in b[-128:] and encrypted=='no','invalid/encrypted PDF')
 return {'pages':pages,'encrypted':encrypted,'bytes':len(b),'sha256':sha(b)}

def verify(repo):
 need(git(repo,'rev-parse',COMMIT+'^').decode().strip()==PARENT,'unexpected parent')
 expected_paths=sorted(d+'/'+f for d in REPORTS.values() for f in ('README.md','article.tex','article.pdf'))
 actual=git(repo,'diff-tree','--no-commit-id','--name-only','-r',COMMIT).decode().splitlines()
 need(sorted(actual)==expected_paths,'unexpected commit scope')
 all_pins=[{'commit':c,'path':p,'bytes':len(pinned(repo,c,p)),'sha256':s} for (c,p),s in sorted(PINS.items())]
 swo=pinned(repo,COMMIT,SWO+'/article.tex').decode();swo_labels=label_list(swo);swo_numbers=number_map(swo)
 need(len(set(swo_labels))==len(swo_labels),'duplicate source labels')
 headings=heading_numbers(swo)
 foundations_headings={'5.3':'Which recursion principle is used?','5.4.4':'Why an ordinal-length recursion here need not invoke ETR','5.5.3':'The precise recursion strength used here','5.6.2':'The recursion principle actually used'}
 for num,title in foundations_headings.items():need(headings.get(num)==title,'foundations subsection reference '+num)
 for lab,num in EXTERNAL_NUMBERS.items():need(swo_numbers.get(lab)==num,'external theorem numbering '+lab)
 need(sha(swo.encode())=='728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503','reviewed synthesis changed')
 results={};totals=collections.Counter();all_paths=set(git(repo,'ls-tree','-r','--name-only',COMMIT).decode().splitlines())
 with tempfile.TemporaryDirectory(prefix='surreal-reciprocal-') as td:
  for key,d in REPORTS.items():
   old=pinned(repo,PARENT,d+'/article.tex').decode();new=pinned(repo,COMMIT,d+'/article.tex').decode()
   need(old.split(r'\begin{document}')[0]==new.split(r'\begin{document}')[0],'preamble/macros changed')
   declared=set(re.findall(r'\\newtheorem\*?\{([^}]+)\}',new))
   need(declared<=set(FORMAL),'uncovered declared formal environments')
   ops=difflib.SequenceMatcher(a=old.splitlines(True),b=new.splitlines(True),autojunk=False).get_opcodes()
   insertions=[]
   for tag,a,b,c,e in ops:
    if tag=='equal':continue
    need(tag=='insert','old TeX changed rather than inserted')
    text=''.join(new.splitlines(True)[c:e]);insertions.append({'old_after_line':a,'new_first_line':c+1,'new_last_line':e,'text':text,'sha256':sha(text.encode())})
   audits={}
   for title,fun in [('formal',lambda s:blocks(s,FORMAL)),('proof',lambda s:blocks(s,('proof',))),('display',displays)]:
    aa=fun(old);bb=fun(new);need([x[2:] for x in aa]==[x[2:] for x in bb],title+' body/order changed')
    audits[title]=[{'index':i,'kind':a[2],'before_line':old.count('\n',0,a[0])+1,'after_line':new.count('\n',0,b[0])+1,'sha256':sha(a[3].encode())} for i,(a,b) in enumerate(zip(aa,bb))]
    totals[title]+=len(aa)
   labels=label_list(old);need(labels==label_list(new) and len(labels)==len(set(labels)),'label list changed or duplicates')
   totals['labels']+=len(labels)
   # Insertions contain no structural/numbering events; all existing numbered
   # statements remain byte-identical, and their preamble and event order agree.
   structure=lambda s:re.findall(r'\\(?:part|chapter|section|subsection|subsubsection|setcounter|addtocounter|numberwithin|counterwithin)\*?(?:\[[^\]]*\])?\{[^}]*\}',uncomment(s))
   need(structure(old)==structure(new),'structural counter event changed')
   added=''.join(x['text'] for x in insertions)
   external=sorted(set(re.findall(r'swo:[A-Za-z0-9:._-]+',added)))
   for lab in external:need(lab in swo_labels,'missing external target '+lab)
   refs=[]
   for m in re.finditer(r'\\(?:[Cc]ref|[Ee]qref|ref)\{([^}]+)\}',added):refs+=m[1].split(',')
   for lab in refs:need(lab in labels,'missing local target '+lab)
   if key=='lwo':
    nums=number_map(new)
    for lab,num in LWO_NUMBERS.items():need(nums.get(lab)==num,'LWO theorem number '+lab)
    for lab in LWO_NUMBERS:need(lab in swo,'claimed pointer absent '+lab)
   rold=pinned(repo,PARENT,d+'/README.md').decode();rnew=pinned(repo,COMMIT,d+'/README.md').decode()
   changes=[]
   for tag,a,b,c,e in difflib.SequenceMatcher(a=rold.splitlines(True),b=rnew.splitlines(True),autojunk=False).get_opcodes():
    if tag=='equal':continue
    before=''.join(rold.splitlines(True)[a:b]);after=''.join(rnew.splitlines(True)[c:e])
    need(tag=='insert' or (key=='hset' and tag=='replace' and '62 pages' in before and 'still 62' in after),'unexpected README edit')
    changes.append({'type':tag,'before_lines':[a+1,b],'after_lines':[c+1,e],'before':before,'after':after})
   links=[]
   for m in re.finditer(r'\]\(([^)]+)\)',''.join(x['after'] for x in changes)):
    target=m[1];need(not '://' in target,'unexpected external web link')
    p=posixpath.normpath(posixpath.join(d,target)).rstrip('/')
    need(p+'/README.md' in all_paths,'broken new relative link '+target);links.append({'link':target,'resolved':p+'/README.md'})
   io=inventory(repo,PARENT,d);inw=inventory(repo,COMMIT,d);need(io.keys()==inw.keys(),'report inventory changed')
   companions=[]
   for p in io:
    if p in expected_paths:continue
    need(io[p]==inw[p],'companion changed '+p);companions.append({'path':p,**io[p]})
   totals['companions']+=len(companions);totals['article_insertions']+=len(insertions);totals['inserted_tex_lines']+=sum(x['new_last_line']-x['new_first_line']+1 for x in insertions)
   po=pdf_summary(pinned(repo,PARENT,d+'/article.pdf'),td);pn=pdf_summary(pinned(repo,COMMIT,d+'/article.pdf'),td)
   need(po['pages']==pn['pages'],'PDF page count changed')
   results[key]={'directory':d,'insertions':insertions,'README_changes':changes,'ordered_exact_blocks':audits,'labels':labels,'structural_events_unchanged':True,'preamble_unchanged':True,'local_added_references':refs,'external_added_references':external,'new_relative_links':links,'unchanged_companions':companions,'PDF_before':po,'PDF_after':pn}
 totals['reports']=4;totals['changed_paths']=len(actual)
 return {'status':'PASS','commit':COMMIT,'parent':PARENT,'scope':'Only four reciprocal notes at the pinned commit; exact preservation plus reference/number/PDF checks, with separate human prose audit. No author suites, TeX rebuild, original-proof re-audit, or machine-checked semantics.','source_sha256':sha(Path(__file__).read_bytes()),'pins':all_pins,'totals':dict(sorted(totals.items())),'external_statement_numbers':EXTERNAL_NUMBERS,'foundations_subsection_numbers':foundations_headings,'lwo_pointer_statement_numbers':LWO_NUMBERS,'reports':results,'new_defects':[]}

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--expect',type=Path);p.add_argument('--write',type=Path);a=p.parse_args()
 need(not(a.expect and a.write),'choose --expect or --write')
 result=verify(a.repo)
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'saved receipt mismatch')
 if a.write:a.write.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','totals':result['totals']},sort_keys=True))
if __name__=='__main__':main()
