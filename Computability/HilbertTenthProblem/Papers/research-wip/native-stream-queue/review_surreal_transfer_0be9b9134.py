#!/usr/bin/env python3
"""Pinned formal/display/label and companion census of the four-source surreal merge.
No source programs or TeX builds are executed. Uses standard-library Python,
read-only Git and pdfinfo for the delivered PDFs.
"""
if not __debug__:raise RuntimeError('Run this pinned audit without -O')
import argparse,collections,hashlib,io,json,re,stat,subprocess,tempfile,zipfile
from pathlib import Path,PurePosixPath
ARRIVAL='4e270aa4648c5fd7e18626507531046715976535'
PLACEMENT='ccc046989e0d9c5556a8d2d8c1b81c3aa85e185d'
FIRST='d51fafea806cbd48ba29be017eff85cdd9653b14'
FINAL='0be9b913487fa2cc0e16cea6545c55f33b4446d8'
TARGET='Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders'
LABEL={'11':'lower1','12':'lower','09':'research','08':'research1'}
PREFIX={'11':'swo:','12':'swo:st:','09':'swo:ec:','08':'swo:sk:'}
PINS={
 (FIRST,'article.tex'):'8e40fe735efd3dfe3dc0b24a6c7cafb642203f43b7e8dc303804633fe7b99611',
 (FIRST,'article.pdf'):'d38c5cb93aa64098aa17a588de667a8ed0433a2faa37f6385d3070a01ef0de67',
 (FINAL,'article.tex'):'728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503',
 (FINAL,'article.pdf'):'4b228811c4719c063aad1932d540e7f0e531ff6a1ca082df014a6fce0d7a2cbf',
 (FINAL,'README.md'):'8fc8b16c54a45cab946f383ee47b9f87b31b105939e0d65f681c88a1f1a6a568'}
NOTATION_PIN='1c6b246bfe5889177a7c9557b9c6d64d3654bfb099a12508ef3904a6c9f052e9'
ARCHIVES=[{'archive': 'Surreal_Well_Orders_Research.zip',
  'label': 'research',
  'members': [{'path': 'surreal_well_orders/README.md',
               'sha256': '7d2a38c8a48685083851ae2e07a39d50a2f0011f5f10a7a13be8cd9983c29ba3',
               'size': 3750},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': 'b583206a78a401a6d40eec3fe2d14a1a4a1232c258cfd9322b6157154180696e',
               'size': 5239},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '66a3c25862ed389c8c46b254da14aa81220213c570844d829036108a463e5b8a',
               'size': 570},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'e368b543d32d374c4e672c945bb3d3f0b0c739f3e8961477f62a5f31c0217105',
               'size': 334883},
              {'path': 'surreal_well_orders/article.tex',
               'sha256': 'bd87c866b520a5261178b28e23fb6df3bcbf2c431bd8414b46f919b022ffc56c',
               'size': 80261},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '3894153b599649376c75971722a7a377ab84b1b34280e80a955dad8b91453a66',
               'size': 221},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '508bf3668241708b72043bff16bb64b559842b745572a2a6f05e4be65a8d2f64',
               'size': 10211},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': '29c3beb5bed2dce88b2a70fa0a55408ce5510b95016b7a93ce705edf28ea9460',
               'size': 576}],
  'sha256': '8aebf0ab80207a4e2165be6f7a329eff18b90134128b02e65c4732c97c252ee9'},
 {'archive': 'Surreal_Well_Orders_Research (1).zip',
  'label': 'research1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': 'd99f4a6c05f37c3a4c61118ceb05d2246f5d6dd2fbccf1fc07a575f665cfc256',
               'size': 352071},
              {'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': '2a3f5c055d64adc4f3954b1c0224e52c710f57873617d3f756c207ed26a4d4a0',
               'size': 95748},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '5f63b9ee2fead063c4a9c23523996d699284acb1e12df8783790483033194eee',
               'size': 3966},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '081a9006286946109415a3b6b04bef6a3087df4c2c8ae015c0f4364725c22ce6',
               'size': 428},
              {'path': 'surreal_well_orders/verify_finite.py',
               'sha256': '2e429bc5a52702a922f44ee60b7e1a91dc9ef9924bc7c8649bfbae2069e843d5',
               'size': 3721},
              {'path': 'surreal_well_orders/verification_results.json',
               'sha256': '6d9bc26ba180fed1832106e605ab3c537b65be7ac481916d301050ddf076cf60',
               'size': 332},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '8fa626f69eb33d7cf8e396cbc2a2a2e02db11170cc7f69d75cfac9172cea600a',
               'size': 506}],
  'sha256': '36c7f6ac22cd2a665aa078eb99eeffef170cb2d6c0cadab31417562f147d8179'},
 {'archive': 'surreal_well_orders.zip',
  'label': 'lower',
  'members': [{'path': 'surreal_well_orders/article.tex',
               'sha256': '44ce2e2de4bdf15373709b6c120be7e03eadd3d868149152fefb409ae0dcd450',
               'size': 79635},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'fee434ab4074dc736846e7322abba97e0c12ad2f3b4f72df39f2a98b606004a4',
               'size': 484264},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '48ec3a58af77dcb314dcb2be5a517a1e405a12ef7e0bc0122d25190b3b93e78a',
               'size': 4326},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': '9536ab4b79e344bd2f6e5c80ffc9e16e0ac1e5bc6f7b289372d04b7d97b74904',
               'size': 8647},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '23e41596cf1fbe0d3d18c48b831c18915bf63b834183d570ae7aef456ba36c68',
               'size': 402},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '2bacfce134b39479d910159486079aa5792550a1fe7e57c54b79d9605827f7a3',
               'size': 7326},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': 'b541630a53904c56aa8fbf2f2e6bb9a1b731735e58473608b44f4e90546e521c',
               'size': 845},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': 'a1118dc2384a9ccf0acf27d43972a9f257b158e24e1ea3aeb105a3f13963a4ba',
               'size': 570}],
  'sha256': '1edf59eaa0febdc0b7c9da581d9a6a65cc2ae88b99c166756ffd58f8aa4d4d5d'},
 {'archive': 'surreal_well_orders (1).zip',
  'label': 'lower1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': 'b08eaac10e7cd7573713490422d6d3a590cdac8df890743b98c07c3f5742dac2',
               'size': 126780},
              {'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': '7dbce2ecb7cd661514465887ff5ab68603ff0c7a46dc9c7f407744a67c513552',
               'size': 543575},
              {'path': 'surreal_well_orders/README.txt',
               'sha256': 'f0b5a8dd762e56fbf58b4bdeeea3eb5be1904926a396c1d2206a9d0ea21e8fd7',
               'size': 2414},
              {'path': 'surreal_well_orders/repository_audit.md',
               'sha256': '9332fff9474586f329927f9fc44c53ba53caf689ed3aee561fa44b4935130f39',
               'size': 10682},
              {'path': 'surreal_well_orders/finite_checks.py',
               'sha256': '751e173bf3529e93d86a0281e1385515ec8220a1b97ca682a2ecef8bd895b844',
               'size': 6538},
              {'path': 'surreal_well_orders/finite_checks_results.txt',
               'sha256': '997710f1aef157365105381378e0d4638f67092c847d3df8a93befbf561f52af',
               'size': 939}],
  'sha256': 'e48ab1b54681787324fd01953ba093d2b7abe546673ccd0f0a0bcb59e232e33a'}]
MAPPING={'09-core-RESEARCH_STATUS.md': ['research', 'RESEARCH_STATUS.md'],
 '11-raw-orders-repository_audit.md': ['lower1', 'repository_audit.md'],
 '12-singular-RESEARCH_STATUS.md': ['lower', 'RESEARCH_STATUS.md'],
 'code/08-skeleton-build.sh': ['research1', 'build.sh'],
 'code/08-skeleton-verify_finite.py': ['research1', 'verify_finite.py'],
 'code/09-core-build.sh': ['research', 'build.sh'],
 'code/09-core-finite_checks.py': ['research', 'code/finite_checks.py'],
 'code/11-raw-orders-finite_checks.py': ['lower1', 'finite_checks.py'],
 'code/12-singular-build.sh': ['lower', 'build.sh'],
 'code/12-singular-finite_checks.py': ['lower', 'code/finite_checks.py'],
 'data/08-skeleton-verification_results.json': ['research1', 'verification_results.json'],
 'data/09-core-finite_checks.json': ['research', 'data/finite_checks.json'],
 'data/11-raw-orders-finite_checks_results.txt': ['lower1', 'finite_checks_results.txt'],
 'data/12-singular-finite_checks.json': ['lower', 'data/finite_checks.json']}
OLD_GBC="For non-set-like relations, the model's class collection can matter to\nthe well-order assertion."
NEW_GBC='Over $\\GBC$, well-foundedness of any fixed class relation is equivalent\nto the absence of a set-coded descending $\\omega$-sequence. Keeping the\nsets and the relation fixed while enlarging the class collection therefore\ndoes not change its internal well-foundedness. What may change is which\nclass relations are available; internal and external well-foundedness\nmust also be distinguished.'
def need(v,s):
 if not v:raise ValueError(s)
def digest(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args],timeout=60)
def blob(repo,commit,path):return git(repo,'show',commit+':'+path)
def uncomment(t):return re.sub(r'(?<!\\)%[^\n]*','',t)
def labels(t):return re.findall(r'\\label(?:\[[^\]]*\])?\{([^}]+)\}',uncomment(t))
def normalize(t,source,original=True):
 """Only explicit source-sensitive notation, label/citation renaming and spacing.
 No algebraic, inequality, sign, quantifier or general prose normalization.
 """
 t=uncomment(t)
 t=re.sub(r'\\label(?:\[[^\]]*\])?\{[^}]+\}','',t)
 if original:
  t=re.sub(r'(\\(?:[Cc]ref|[Ee]qref|ref|pageref)\{)([^}]+)(\})',lambda m:m[1]+','.join(PREFIX[source]+v.strip() for v in m[2].split(','))+m[3],t)
  # The only changed citation key occurring inside a copied statement body.
  t=re.sub(r'(\\cite(?:\[[^\]]*\])?\{)HW(\})',lambda m:m[1]+'HamkinsWoodin'+m[2],t)
  if source=='11':
   t=t.replace(r'X_\kappa=\No_{<\kappa}',r'\No_{<\kappa}')
   t=t.replace(r'\ell(',r'\bd(').replace(r'X_\kappa',r'\No_{<\kappa}')
   for v in ('lambda','kappa'):t=t.replace('\\mathcal P_\\'+v,'\\WO_\\'+v)
  elif source=='12':
   t=re.sub(r'(?<![A-Za-z\\])b\(',lambda _:r'\bd(',t)
   t=t.replace(r'S_\kappa',r'\No_{<\kappa}').replace(r'S_{<\theta}',r'\No_{<\theta}')
   t=t.replace(r'\WO_{\mathrm{cl}}',r'\Hall').replace(r'\WO_{\rm cl}',r'\Hall')
   for a,b in [('SL','Hsl'),('CC','BOrd'),('rk','bl')]:t=re.sub(r'\\'+a+r'\b',lambda m:'\\'+b,t)
  elif source=='09':
   t=t.replace(r'X_\theta=\No_{<\theta}',r'\No_{<\theta}')
   t=t.replace(r'\Core_b^{<\kappa}',r'\Psupp^{<\kappa}(b)').replace(r'\Core_b',r'\Psupp(b)')
   t=re.sub(r'X_(\{[^}]+\}|\\[A-Za-z]+|[A-Za-z])',lambda m:r'\No_{<'+m[1].strip('{}')+'}',t)
   for a,b in [('GE','Hsl'),('Tree','Words')]:t=re.sub(r'\\'+a+r'\b',lambda m:'\\'+b,t)
  else:
   t=t.replace(r'X_\lambda=\No_{<\lambda}',r'\No_{<\lambda}')
   t=t.replace(r'X_\lambda',r'\No_{<\lambda}').replace(r'X_\kappa',r'\No_{<\kappa}')
   # Power sets keep their meaning; the core's macro is a distinct context.
   t=t.replace(r'\Pset(\mathbb N)',r'\mathcal P(\mathbb N)').replace(r'\Pset(V_\kappa)',r'\mathcal P(V_\kappa)')
   t=t.replace(r'\Pset_b',r'\Psupp(b)')
   t=re.sub(r'\\Pset\b',lambda _:r'\Psupp',t);t=re.sub(r'\\E\b',lambda _:r'\Hsl',t)
   t=re.sub(r'\\tag\{(\d+)\}',lambda m:r'\tag{S08.'+m[1]+'}',t)
 return re.sub(r'\s+','',t)
ENVS='theorem|lemma|proposition|corollary|definition|example|remark|question|note'
def formals(t):
 t=uncomment(t);sec=counter=0;out=[]
 for m in re.finditer(r'\\section\*?\{|\\begin\{('+ENVS+r')\}',t):
  if m[0].startswith(r'\section'):sec+=1;counter=0;continue
  env=m[1];end=t.find('\\end{'+env+'}',m.end());need(end>=0,'Unclosed formal environment')
  body=re.sub(r'^\[[^\]]*\]','',t[m.end():end]);counter+=1
  out.append(dict(number=f'{sec}.{counter}',env=env,body=body,line=t.count('\n',0,m.start())+1,labels=labels(body)))
 return out
def displays(t):
 pattern=r'(?<!\\)\\\[(.*?)(?<!\\)\\\]|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*?)\\end\{\2\}'
 return [dict(text=m[1] if m[1]is not None else m[3],line=t.count('\n',0,m.start())+1) for m in re.finditer(pattern,uncomment(t),re.S)]
def math_norm(t,source,original):return re.sub(r'\\tag\{[^}]+\}','',normalize(t,source,original))
def lcs_pairs(a,b):
 # Ordered occurrence matching: indices advance strictly in both lists.
 n,m=len(a),len(b);table=[[0]*(m+1) for _ in range(n+1)]
 for i in range(n-1,-1,-1):
  for j in range(m-1,-1,-1):table[i][j]=1+table[i+1][j+1] if a[i]==b[j] else max(table[i+1][j],table[i][j+1])
 i=j=0;pairs=[]
 while i<n and j<m:
  if a[i]==b[j]:pairs.append((i,j));i+=1;j+=1
  elif table[i+1][j]>=table[i][j+1]:i+=1
  else:j+=1
 return pairs
def balanced(t,start):
 need(t[start]=='{','Expected brace');depth=0
 for i in range(start,len(t)):
  if i and t[i-1]=='\\':continue
  if t[i]=='{':depth+=1
  elif t[i]=='}':
   depth-=1
   if depth==0:return t[start+1:i],i+1
 raise ValueError('Unclosed brace')
def macros(t):
 out={}
 for m in re.finditer(r'\\newcommand\{\\([A-Za-z]+)\}(?:\[(\d+)\])?\s*\{',t):
  body,end=balanced(t,m.end()-1);out[m[1]]=dict(arity=int(m[2] or 0),definition=body)
 return out

def run(repo):
 repo=Path(repo).resolve()
 for commit in (ARRIVAL,PLACEMENT,FIRST,FINAL):need(git(repo,'rev-parse',commit).decode().strip()==commit,'Immutable commit mismatch')
 originals={};inventory=[]
 for arc in ARCHIVES:
  data=blob(repo,ARRIVAL,'docs/incoming/'+arc['archive']);need(digest(data)==arc['sha256'],'Archive hash')
  files={}
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   need(sum(i.file_size for i in z.infolist())<32*1024*1024,'ZIP size cap')
   seen=set()
   for info in z.infolist():
    name=info.filename;p=PurePosixPath(name)
    need(not p.is_absolute() and '..'not in p.parts and '\\'not in name and name not in seen and not stat.S_ISLNK(info.external_attr>>16),'Unsafe ZIP entry');seen.add(name)
    if not info.is_dir():files[name]=z.read(info)
  found=[dict(path=n,size=len(b),sha256=digest(b)) for n,b in sorted(files.items())]
  need(exact(found,sorted(arc['members'],key=lambda x:x['path'])),'Complete member manifest')
  originals[arc['label']]=files;inventory.append(dict(archive=arc['archive'],sha256=digest(data),members=found))
 authenticated={};pins=[]
 for (commit,name),sha in PINS.items():
  b=blob(repo,commit,TARGET+'/'+name);need(digest(b)==sha,'Placed source/PDF pin');authenticated[(commit,name)]=b;pins.append(dict(commit=commit,path=TARGET+'/'+name,bytes=len(b),sha256=sha))
 notation=blob(repo,FINAL,'Algebra/SurrealNumbers/docs/NOTATION.md');need(digest(notation)==NOTATION_PIN,'Notation guide pin')
 pins.append(dict(commit=FINAL,path='Algebra/SurrealNumbers/docs/NOTATION.md',bytes=len(notation),sha256=NOTATION_PIN))
 article=authenticated[(FINAL,'article.tex')].decode();readme=authenticated[(FINAL,'README.md')].decode()
 source={s:next(b.decode() for n,b in originals[label].items() if n.endswith('.tex')) for s,label in LABEL.items()}
 transfers=[];retained=set()
 for name,(label,member) in sorted(MAPPING.items()):
  original=originals[label]['surreal_well_orders/'+member];retained.add((label,'surreal_well_orders/'+member))
  for commit in (PLACEMENT,FIRST,FINAL):need(blob(repo,commit,TARGET+'/'+name)==original,'Companion changed '+name)
  transfers.append(dict(path=name,source=label,member='surreal_well_orders/'+member,bytes=len(original),sha256=digest(original)))
 names=git(repo,'ls-tree','-r','--name-only',FINAL,'--',TARGET).decode().splitlines()
 need(names==sorted(TARGET+'/'+n for n in list(MAPPING)+['article.tex','article.pdf','README.md']),'Unexpected final report inventory')
 archived=[]
 for label,files in originals.items():
  for name,b in sorted(files.items()):
   if (label,name)not in retained:archived.append(dict(source=label,member=name,bytes=len(b),sha256=digest(b),status='Original archive retained at arrival; manuscript/README text synthesized or original PDF/manifest superseded in presentation'))
 need(len(transfers)==14 and len(archived)==15,'Companion accounting')
 # All original labels survive exactly once; the 74 new labels are explicit.
 target_labels=labels(article);need(len(target_labels)==272 and len(set(target_labels))==272,'Final label uniqueness/count')
 labels_result=[]
 for s,t in source.items():
  old=labels(t);mapped=[PREFIX[s]+n for n in old]
  need(len(old)==len(set(old)) and all(target_labels.count(n)==1 for n in mapped),'Original source label missing/repeated')
  labels_result.append(dict(source=s,original_labels=len(old),mapped_labels=mapped,new_labels=sorted(n for n in target_labels if n.startswith(PREFIX[s]) and n not in mapped and (s!='11' or not n.startswith(('swo:st:','swo:ec:','swo:sk:'))))))
 need(sum(x['original_labels'] for x in labels_result)==198,'Original label count')
 refs=[v.strip() for m in re.finditer(r'\\(?:[Cc]ref|[Ee]qref|ref|pageref)\{([^}]+)\}',uncomment(article)) for v in m[1].split(',')]
 need(all(v in target_labels for v in refs),'Unresolved internal reference')
 tf=formals(article);bylabel={label:f for f in tf for label in f['labels']};formal_records=[];totals=collections.Counter();summaries=[]
 for s,t in source.items():
  old=formals(t);records=[]
  for f in old:
   key=PREFIX[s]+(f['labels'][0] if f['labels'] else 'n'+f['number']);need(key in bylabel,'Unmapped numbered statement '+key);g=bylabel[key]
   a,b=normalize(f['body'],s),normalize(g['body'],s,False)
   if a==b:
    need(f['env']==g['env'],'Unexpected copied environment change');mode='normalized_exact_body'
   elif g['env']=='note':mode='declared_duplicate_note_semantic_review_separate'
   else:
    need(s=='12' and f['number']=='14.5' and g['env']=='remark','Unexplained copied statement change '+key)
    prefix=normalize(r"\emph{Source 12's text:}",s,False)
    need(b.startswith(prefix+a) and r'\merge' in b[len(prefix+a):],'Original question not preserved inside augmented remark')
    mode='verbatim_question_inside_editorial_answer'
   totals[mode]+=1
   record=dict(source=s,number=f['number'],original_environment=f['env'],target_environment=g['env'],label=key,source_line=f['line'],target_line=g['line'],mode=mode,
    original_normalized_sha256=digest(a.encode()),target_normalized_sha256=digest(b.encode()))
   records.append(record);formal_records.append(record)
  # The crosswalk itself must list every original occurrence in original order.
  cross=article[article.index(r'\subsection{Source '+s+(' (base)' if s=='11' else '')+'}',article.index('% ---- generated crosswalk')):]
  cross=cross.split(r'\end{longtable}',1)[0]
  actual=re.findall(r'^(\d+\.\d+)\s*&.*?\\Cref\{([^}]+)\}',cross,re.M)
  need(actual==[(r['number'],r['label']) for r in records],'Crosswalk order/multiplicity changed')
  order=[r['target_line'] for r in records];ordered=lcs_pairs(order,sorted(order))
  if s=='11':need(len(ordered)==len(records),'Base source formal order changed')
  summaries.append(dict(source=s,numbered_statements=len(records),modes=dict(collections.Counter(r['mode'] for r in records)),longest_subsequence_in_target_order=len(ordered),full_original_order_claimed=(s=='11')))
 need(totals==dict(normalized_exact_body=124,declared_duplicate_note_semantic_review_separate=41,verbatim_question_inside_editorial_answer=1),'Formal classification count')
 # Each of the 100 declared source chunks is compared locally, respecting the
 # manuscript's own source-line and display occurrence order. Global thematic
 # reorderings of sources08/09/12 are not hidden by an unordered multiset.
 pattern=r'^% ---- (?:source (\d+), lines (\d+)-(\d+)|hand chunk[^\n]*|generated crosswalk[^\n]*)$'
 marks=list(re.finditer(pattern,article,re.M));chunk_records=[];display_counts=collections.Counter();covered={s:set() for s in source}
 for i,m in enumerate(marks):
  if not m[1]:continue
  s,lo,hi=m[1],int(m[2]),int(m[3]);original='\n'.join(source[s].splitlines()[lo-1:hi]);end=marks[i+1].start() if i+1<len(marks) else len(article);target=article[m.end():end]
  covered[s].update(range(lo,hi+1));a,b=displays(original),displays(target)
  aa=[math_norm(x['text'],s,True) for x in a];bb=[math_norm(x['text'],s,False) for x in b]
  pairs=lcs_pairs(aa,bb);need(pairs==[(j,j) for j in range(len(aa))] and len(aa)==len(bb),'Changed/missing/reordered copied display '+s+':'+str(lo))
  display_counts[s]+=len(a);target_start=article.count('\n',0,m.end())+1
  chunks=dict(source=s,source_start=lo,source_end=hi,target_start=target_start,target_end=article.count('\n',0,end)+1,
   original_chunk_sha256=digest(original.encode()),target_chunk_sha256=digest(target.encode()),display_occurrences=[dict(source_line=lo+x['line']-1,target_line=target_start+y['line']-1,normalized_sha256=digest(aa[j].encode())) for j,(x,y) in enumerate(zip(a,b))])
  # All full copied formal bodies are already checked against labelled targets.
  chunk_records.append(chunks)
 need(len(chunk_records)==100 and dict(display_counts)=={'11':56,'12':24,'09':22,'08':10},'Copied chunk/display counts')
 global_displays=[]
 td=displays(article)
 for s,t in source.items():
  ds=displays(t);a=[math_norm(x['text'],s,True) for x in ds];b=[math_norm(x['text'],s,False) for x in td];pairs=lcs_pairs(a,b)
  global_displays.append(dict(source=s,original_display_occurrences=len(ds),displays_in_copied_source_chunks=display_counts[s],outside_copied_chunks=[x['line'] for x in ds if x['line']not in covered[s]],
   global_ordered_exact_subsequence=len(pairs),global_ordered_pairs=[dict(source_line=ds[i]['line'],target_line=td[j]['line'],normalized_sha256=digest(a[i].encode())) for i,j in pairs],
   scope='Diagnostic ordered subsequence only. Global display preservation is not asserted for declared condensed proof notes or thematic reordering.'))
 old_tags=re.findall(r'\\tag\{(\d+)\}',source['08']);new_tags=re.findall(r'\\tag\{S08\.(\d+)\}',article)
 need(old_tags==[str(i) for i in range(1,14)] and new_tags==[str(i) for i in range(1,14) if i!=10],'Source08 equation-tag accounting')
 need('its display (S08.10) is the inequality $a\\le b$' in article,'Disclosed nondisplayed tag10 missing')
 # Expose every common macro's exact definition and explicitly name the
 # source-sensitive collisions, rather than interpreting all \rk alike.
 target_macros=macros(article);macro_records=[]
 maps={'11':{},'12':{'SL':'Hsl','CC':'BOrd','rk':'bl'},'09':{'GE':'Hsl','Core':'Psupp','Tree':'Words'},'08':{'E':'Hsl','Pset':'Psupp'}}
 for s,t in source.items():
  for name,definition in macros(t).items():
   newname=maps[s].get(name,name);need(newname in target_macros,'Undefined renamed macro '+name);new=target_macros[newname]
   need(definition['arity']==new['arity'],'Macro argument arity changed')
   macro_records.append(dict(source=s,old_command=name,new_command=newname,old=definition,new=new,literal_definition_preserved=(definition==new),scope='Explicit notation unification; Pset power-set uses are retained literally as mathcal P, while its core uses Psupp.'))
 # The known original08 correction is tested only within its copied chunk,
 # not confused with the nearby editorial quotation of the old sentence.
 correction=next(c for c in chunk_records if c['source']=='08' and c['source_start']==731)
 text='\n'.join(article.splitlines()[correction['target_start']-1:correction['target_end']-1])
 need(OLD_GBC in source['08'] and normalize(NEW_GBC,'08',False) in normalize(text,'08',False),'Known fixed-relation correction missing')
 need(normalize(OLD_GBC,'08',False)not in normalize(text,'08',False),'Old GBC assertion retained in active source chunk')
 # PDF parsing only authenticates delivered output/page counts. It is not a
 # fresh TeX build or proof that every displayed glyph reproduces the TeX.
 pdf_checks=[]
 with tempfile.TemporaryDirectory(prefix='surreal-transfer-pdf-') as td0:
  todo=[('merged',authenticated[(FINAL,'article.pdf')],115)]+[(s,next(b for n,b in originals[LABEL[s]].items() if n.endswith('.pdf')),{'11':35,'12':24,'09':24,'08':26}[s]) for s in LABEL]
  for label,data,want in todo:
   path=Path(td0)/(label+'.pdf');path.write_bytes(data)
   info=subprocess.check_output(['pdfinfo',str(path)],text=True,timeout=30)
   pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]);need(pages==want and data.startswith(b'%PDF-'),'Delivered PDF pages/header')
   need(re.search(r'^Encrypted:\s+no',info,re.M)is not None,'Unexpected encrypted PDF')
   pdf_checks.append(dict(source=label,sha256=digest(data),bytes=len(data),pages=pages,encrypted=False))
 allmembers=[dict(source=arc['label'],**member) for arc in ARCHIVES for member in arc['members']]
 biggest=max(allmembers,key=lambda m:m['size']);nonpdf=max((m for m in allmembers if not m['path'].endswith('.pdf')),key=lambda m:m['size'])
 need(biggest['size']==543575 and nonpdf['size']==126780 and 'largest delivered file is\n126,780 bytes' in readme,'Pinned README size finding changed')
 return dict(status='PASS_PRESERVATION_WITH_SEPARATE_EDITORIAL_CORRECTIONS',arrival=ARRIVAL,placement=PLACEMENT,first_write=FIRST,final_write=FINAL,
  checker_sha256=digest(Path(__file__).read_bytes()),authenticated_presentation=pins,archives=inventory,byte_exact_companions=transfers,originals_retained_only_in_arrival=archived,
  labels=labels_result,reference_occurrences_resolved=len(refs),final_unique_labels=272,numbered_statement_summary=summaries,numbered_statements=formal_records,
  copied_source_chunks=chunk_records,ordered_display_diagnostics=global_displays,source08_equation_tags=dict(original=old_tags,displayed=new_tags,described_not_displayed=['10']),macro_census=macro_records,pdfs=pdf_checks,
  known_GBC_sentence_correction=dict(applied=True,original=OLD_GBC,replacement=NEW_GBC,target_line=correction['target_start']),
  size_finding=dict(readme_phrase='largest delivered file is 126,780 bytes',largest_actual_member=biggest,largest_non_PDF_member=nonpdf,suggested_text='largest delivered non-PDF file is 126,780 bytes'),
  counts=dict(archives=4,members=29,unchanged_companions=14,archived_presentation_members=15,original_labels=198,new_labels=74,numbered_statements=166,normalized_exact_statement_bodies=124,declared_duplicate_notes=41,question_retained_in_augmented_remark=1,copied_chunks=100,ordered_copied_displays=112,executed_author_programs=0,TeX_builds=0),
  scope='Formal/display/label/provenance transfer at the two immutable write commits. All original statement crosswalk occurrences and local copied-display orders are preserved. Duplicate-note semantics and new synthesis claims are independently reviewed in the companion editorial audit; this is not a full new theorem review or an all-occurrences-verbatim claim.')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved exact receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
