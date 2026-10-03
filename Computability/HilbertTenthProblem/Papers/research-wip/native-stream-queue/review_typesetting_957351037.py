#!/usr/bin/env python3
"""Read-only, pinned semantic-transcription census for 957351037.

No archived code is executed. verify(repo) reads immutable Git blobs and ZIP
members in memory. Textual normalization is not a TeX parser or theorem prover.
The literal point-source/dipole fixture is independent of author implementations.
"""
from pathlib import Path, PurePosixPath
from fractions import Fraction
import argparse, collections, difflib, hashlib, io, json, re, subprocess, zipfile

SNAPSHOTS = [{'commit': '957351037', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/article.tex', 'sha256': '6533bb6e13149da0ae41eb010166ef42d32d6996794e76fb3dae56f632a707a8', 'bytes': 545659}, {'commit': '957351037', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/README.md', 'sha256': '8c651e99a35eedd1b52dfd0387e694fb3520e13dcd58b2c263a2a3e6911e9780', 'bytes': 60402}, {'commit': '957351037^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/article.tex', 'sha256': 'b2c63eadf02c8dec76978d42d39bd25d6ee00ee2464aea53cb0c3a7480cfb432', 'bytes': 275767}, {'commit': '957351037^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/README.md', 'sha256': '64e100a14374e8c230947f20b6b657476c25a6998942cd991d55541369e7ef30', 'bytes': 33481}]
ARCHIVES = [{'case': 'mixing', 'archive': 'Mixing_Does_Not_Remove_Arithmetic.zip', 'arrival': 'ef2fc7990', 'sha256': '8c3543f514df39f26f5668d5434ddaa50580aab0303ef84dc6c286731c50c1ca'}, {'case': 'green', 'archive': 'Coercive_Green_Diophantine.zip', 'arrival': 'ef2fc7990', 'sha256': '8e2830036ad0a465f729d4729835b350ea288f758fd8bac8a3ac179ebe368d7a'}, {'case': 'connected', 'archive': 'Well_Conditioned_Diophantine_Computation.zip', 'arrival': 'ef2fc7990', 'sha256': '9cd194e2d3b1cd7814ad465c1c4abae8966b6c7bb0b5a13d1955d17aba159258'}]
CORRECTION = {'old_tex': '\\wtag\\ \\emph{The common theorem.} A branch-history lift of counter machines makes every component of the configuration graph a rooted finite path or a rooted ray. The grounded operator, $\\alpha I-A$ in source~12 and $mI-J$ in source~13, is uniformly coercive, and its Green column at an empty-history source has finite support, a rational root value and a primitive continuant certificate exactly when the computation halts; the resistance is rational or a fixed quadratic irrational, and no computable function bounds support, charge or time. Statement by statement:', 'new_tex': '\\wtag\\ \\emph{The common theorem.} A branch-history lift of counter machines makes every component of the configuration graph a rooted finite path or a rooted ray. The path operators, $L_\\alpha=\\alpha I-A$ in source~12 and $A^{\\rm path}_m=mI-J_P$ in source~13, are uniformly coercive for $\\alpha,m\\geq3$. Their Green columns at the chosen initial-history roots have finite support, a rational root value and a primitive continuant certificate exactly when the computation halts. Source~13 realizes this classification on its connected graph with $A_m=mI-J$, $m\\geq5$, using the antisymmetric dipole response $A_m^{-1}(\\delta_{s_x^+}-\\delta_{s_x^-})$; a point-source column of this connected operator always has infinite support (Proposition~\\ref{ste:wc:prop:positive}). Its two-terminal resistance is twice the path root value: $2D_{L-1}/D_L$ on halting inputs and $m-\\sqrt{m^2-4}$ otherwise. No computable function bounds support, charge or time. Statement by statement:', 'old_readme': 'All six Parts share one pattern', 'new_readme': 'All five Parts share one pattern'}

BASE = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/'
REV = '957351037'
CASES = {'mixing':('Mixing_Does_Not_Remove_Arithmetic/article.tex','ste:mx:'),
 'green':('Coercive_Green_Diophantine/article.tex','ste:cg:'),
 'connected':('well_conditioned_diophantine/article.tex','ste:wc:')}
REVIEWS = [('review_mixing_aebfa386e.md','5b633fcf9'),
 ('review_coercive_connected_aebfa386e.md','899391bde'),
 ('connected_cross_routing_slp.md','9bc875b6a'),('review_connected_cross_routing_slp.md','9bc875b6a')]
def require(ok,message):
 if not ok: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def git(repo,*a):return subprocess.run(['git','-C',str(repo),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def blob(repo,rev,p):return git(repo,'show',rev+':'+p)
def norm(t,refs=True):
 t=re.sub(r'(?<!\\)%[^\n]*','',t)
 t=re.sub(r'\\label(?:\[[^]]+\])?\{[^}]+\}','',t)
 t=re.sub(r'ste:(mx|cg|wc):','',t)
 t=re.sub(r'(\\cite(?:\[[^]]*\])?\{)([^}]*)(\})',lambda m:m[1]+','.join(re.sub(r'^(mx:|cg:|wc:)','',k.strip()) for k in m[2].split(','))+m[3],t)
 t=re.sub(r'\\(?:notag|nonumber|displaystyle|textstyle)\b','',t)
 if refs:
  # Written-out cleveref labels are reviewed in the companion note; no formula is discarded.
  t=re.sub(r'(?:(?:Theorems?|Lemmas?|Propositions?|Corollary|Corollaries|Sections?)[~\s]*)?\\(?:[cC]ref|ref)\{([^}]+)\}',lambda m:''.join('\\RREF{'+k.strip()+'}' for k in m[1].split(',')),t)
  t=re.sub(r'(\\RREF\{[^}]+\})(?:\s|~|,|and)+(?=\\RREF)',r'\1',t)
 return re.sub(r'\s+','',t)
def labels(t):return re.findall(r'\\label(?:\[[^]]+\])?\{([^}]+)\}',t)
def envs(t,e):return re.findall(r'\\begin\{'+re.escape(e)+r'\}(.*?)\\end\{'+re.escape(e)+r'\}',t,re.S)
def displays(t):return sum([envs(t,e) for e in ('equation','equation*','align','align*','gather','gather*')],[])+re.findall(r'(?<!\\)\\\[(.*?)\\\]',t,re.S)
def scoped(t,case):
 if case=='mixing':
  a=t.index(r'\part{Mixing does');b=t.index(r'\part{Coercive Green')
  c=t.index(r'\section{Proof dependency and scope ledger}');d=t.index(r'\section{Compiler and verifier specifications}')
 elif case=='green':
  a=t.index(r'\part{Coercive Green');b=t.index(r'\section*{Part V.B:')
  c=t.index(r'\section{Compiler and verifier specifications}');d=t.index(r'\section{The modular bound as executable pseudocode}')
 else:
  a=t.index(r'\section*{Part V.B:');b=t.index(r'\appendix',a)
  c=t.index(r'\section{The modular bound as executable pseudocode}');d=t.index(r'\begin{thebibliography}',c)
 return t[a:b]+'\n'+t[c:d]
def macro_defs(t):
 d={a or b:v for a,b,v in re.findall(r'\\(?:newcommand|renewcommand)\*?(?:\{(\\\w+)\}|(\\\w+))([^\n]*)',t)}
 for name,body in re.findall(r'\\DeclareMathOperator\{([^}]+)\}\{([^}]+)\}',t):d[name]='{\\operatorname{'+body+'}}'
 return d
def macro_norm(t):return re.sub(r'\s+','',t.replace(r'\left','').replace(r'\right',''))
def compare(old,full_new,case,prefix):
 new=scoped(full_new,case);ol=labels(old);nl=labels(new)
 require(all(prefix+x in nl for x in ol),'original label missing');require(len(nl)==len(set(nl)),'duplicate label')
 counts=collections.Counter(norm(x) for x in displays(new))
 for x in displays(old):
  a=norm(x);require(counts[a]>0,'changed original displayed formula');counts[a]-=1
 st=ss=raws=0
 for e in ('theorem','lemma','proposition','corollary','definition','remark','example','question'):
  nb=envs(new,e)
  for b in envs(old,e):
   ls=labels(b)
   if not ls:continue
   q=[x for x in nb if prefix+ls[0] in labels(x)];require(len(q)==1,'statement label lost');st+=1
   require(norm(b)==norm(q[0]),'statement changed: '+ls[0]);ss+=1
   raws+=norm(b,False)==norm(q[0],False)
 counts=collections.Counter(norm(x) for x in envs(new,'proof'));rawcounts=collections.Counter(norm(x,False) for x in envs(new,'proof'));ps=rawp=0
 for b in envs(old,'proof'):
  a=norm(b);require(counts[a]>0,'original proof changed');counts[a]-=1;ps+=1
  a=norm(b,False)
  if rawcounts[a]>0:rawp+=1;rawcounts[a]-=1
 nm=macro_defs(full_new);md=[]
 for name,body in macro_defs(old).items():
  if name in (r'\headrulewidth',r'\pin'):continue
  require(name in nm and macro_norm(body)==macro_norm(nm[name]),'mathematical macro changed: '+name);md.append(name)
 return {'original_labels':len(ol),'all_original_labels_present':True,'matching_restricted_to_source_main_and_appendices':True,
 'display_blocks':len(displays(old)),'exact_normalized_displays':len(displays(old)),
 'labelled_statements':st,'exact_normalized_statements':ss,'statements_before_reference_expansion_normalization':raws,
 'original_proofs':len(envs(old,'proof')),'exact_normalized_proofs':ps,'proofs_before_reference_expansion_normalization':rawp,
 'preserved_mathematical_macro_definitions':md}
def placed(case,name):
 rel='/'.join(PurePosixPath(name).parts[1:]);p=PurePosixPath(rel)
 if case=='mixing':
  if rel.startswith('code/') or rel=='reproduce.sh':return 'code/11-mixing-arithmetic-'+p.name
  if rel.startswith(('examples/','verification/')) or rel in ('provenance.json','requirements.txt'):return 'data/11-mixing-arithmetic-'+p.name
 elif case=='green':
  if rel.startswith('code/'):return 'code/12-coercive-green-'+p.name
  if rel.startswith('examples/') or rel=='validation/results.json':return 'data/12-coercive-green-'+p.name
  if rel=='SOURCE_AUDIT.md':return '12-coercive-green-SOURCE_AUDIT.md'
 else:
  if rel.startswith('src/') or rel in ('verify.py','build.sh'):return 'code/13-well-conditioned-'+p.name
  if rel.startswith('examples/') or rel=='verification.json':return 'data/13-well-conditioned-'+p.name
  if rel=='sources.md':return '13-well-conditioned-sources.md'
 return None

def point_source_fixture():
 # The source-13 attachment graph for a program consisting of HALT only:
 # all computational path components are isolated vertices, indexed by n>=0.
 def neighbors(v):
  kind,n=v
  if kind in ('+','-'):return [('c',n)]
  if kind=='c':return [('+',n),('-',n),('d',n)]
  return [('c',n),('d',n+1)]+([('d',n-1)] if n else [])
 source={('+',0):1,('-',0):-1};u={('+',0):Fraction(1,5),('-',0):Fraction(-1,5)}
 rows=set(source)|set(u)
 for v in u:rows.update(neighbors(v))
 residuals={str(v):str(5*u.get(v,0)-sum(u.get(w,0) for w in neighbors(v))-source.get(v,0)) for v in rows}
 require(all(x=='0' for x in residuals.values()),'dipole rows failed')
 # All other rows vanish because they touch neither support nor source.
 walks=[]
 for n in range(32):
  walk=[('+',0),('c',0)]+[('d',j) for j in range(n+1)]
  require(all(b in neighbors(a) for a,b in zip(walk,walk[1:])),'walk not in actual attachment graph')
  exponent=len(walk);lower=Fraction(1,5**exponent);require(lower>0,'nonpositive Neumann contribution')
  walks.append({'backbone_index':n,'walk_length':len(walk)-1,'inverse_entry_lower_bound':str(lower)})
 require(u[('+',0)]-u[('-',0)]==Fraction(2,5),'wrong dipole resistance')
 return {'scope':'Immediate HALT attachment graph; every exterior row paid by support-neighbor closure. Infinite point-source support follows from the symbolic walk family, not from truncation.',
  'diagonal':5,'halt_configurations':1,'dipole_support':2,'complete_potentially_nonzero_rows':dict(sorted(residuals.items())),
  'dipole_resistance':'2/5','primitive_integer_charge':5,'point_source_strict_lower_bound_at_d_n':'5^(-n-3) for every n>=0',
  'explicit_walks':walks}

def verify(repo):
 repo=Path(repo);snaps={};out={'status':'PASS_WITH_EDITORIAL_CORRECTIONS','snapshots':SNAPSHOTS,'archives':[],'comparisons':{},'prior_review_pins':[]}
 for sp in SNAPSHOTS:
  b=blob(repo,sp['commit'],sp['path']);require(sha(b)==sp['sha256'] and len(b)==sp['bytes'],'snapshot pin mismatch');snaps[(sp['commit'],sp['path'])]=b.decode()
 changed=git(repo,'diff-tree','--no-commit-id','--name-only','-r',REV).decode().splitlines()
 require(set(changed)=={BASE+x for x in ('article.tex','article.pdf','README.md')},'unexpected non-typesetting change')
 out['commit']={'revision':git(repo,'rev-parse',REV).decode().strip(),'parent':git(repo,'rev-parse',REV+'^').decode().strip(),'changed_files':[{'path':p,'sha256':sha(blob(repo,REV,p)),'bytes':len(blob(repo,REV,p))} for p in changed]}
 text=snaps[(REV,BASE+'article.tex')]
 for sp in ARCHIVES:
  b=blob(repo,sp['arrival'],'docs/incoming/'+sp['archive']);require(sha(b)==sp['sha256'],'archive pin mismatch');members={};records=[];maps=[]
  with zipfile.ZipFile(io.BytesIO(b)) as z:
   for i in z.infolist():
    if i.is_dir():continue
    p=PurePosixPath(i.filename);require(not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and i.filename not in members,'unsafe member');require((i.external_attr>>16)&0o170000 != 0o120000,'symlink member')
    data=z.read(i);members[i.filename]=data;records.append({'path':i.filename,'sha256':sha(data),'bytes':len(data)})
    target=placed(sp['case'],i.filename)
    if target:
     require(blob(repo,REV,BASE+target)==data,'placed delivery changed');maps.append({'member':i.filename,'placed_path':BASE+target,'sha256':sha(data)})
  article,prefix=CASES[sp['case']];out['comparisons'][sp['case']]=compare(members[article].decode(),text,sp['case'],prefix)
  out['archives'].append({**sp,'members':records,'byte_identical_placed_members':maps})
 for name,rev in REVIEWS:
  p='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'+name;b=blob(repo,rev,p)
  out['prior_review_pins'].append({'path':p,'commit':rev,'sha256':sha(b),'bytes':len(b)})
 readme=snaps[(REV,BASE+'README.md')];require(text.count(CORRECTION['old_tex'])==1 and readme.count(CORRECTION['old_readme'])==1,'correction target changed')
 corrected_tex=text.replace(CORRECTION['old_tex'],CORRECTION['new_tex']);corrected_readme=readme.replace(CORRECTION['old_readme'],CORRECTION['new_readme'])
 patch=''
 for name,a,b in [('article.tex',text,corrected_tex),('README.md',readme,corrected_readme)]:patch+=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+BASE+name,tofile='b/'+BASE+name))
 out['suggested_editorial_correction']={'patch_sha256':sha(patch.encode()),'corrected_article_sha256':sha(corrected_tex.encode()),'corrected_readme_sha256':sha(corrected_readme.encode()),'repo_files_edited':False}
 out['point_source_counterexample']=point_source_fixture()
 out['totals']={k:sum(v[k] for v in out['comparisons'].values()) for k in ('original_labels','display_blocks','exact_normalized_displays','labelled_statements','exact_normalized_statements','original_proofs','exact_normalized_proofs')}
 out['totals']['mathematical_macros']=sum(len(v['preserved_mathematical_macro_definitions']) for v in out['comparisons'].values())
 out['totals']['archive_members']=sum(len(v['members']) for v in out['archives']);out['totals']['unchanged_placed_members']=sum(len(v['byte_identical_placed_members']) for v in out['archives'])
 out['scope']={'author_code_executed':False,'historical_parts_I_III_reaudited':False,'pdf_layout_or_build_reaudited':False,'new_editorial_claims_read_in_companion_note':True,'future_revisions_covered':False,'normalization_is_a_formal_proof':False}
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--receipt',type=Path,default=Path(__file__).with_suffix('.json'));p.add_argument('--write',action='store_true');a=p.parse_args();r=verify(a.repo)
 if a.write:a.receipt.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 else:require(exact(r,json.loads(a.receipt.read_text())),'saved receipt mismatch')
 print(json.dumps({'status':r['status'],'totals':r['totals']},sort_keys=True))
if __name__=='__main__':main()
