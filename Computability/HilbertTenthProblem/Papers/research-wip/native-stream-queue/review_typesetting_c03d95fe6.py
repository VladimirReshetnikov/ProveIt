#!/usr/bin/env python3
"""Pinned semantic-transcription census; read-only Git, no author code execution.

verify(repo) reads the two fixed typesetting revisions and four immutable ZIP blobs.
Normalization is textual evidence, not a TeX parser or a proof of a new theorem.
Only labels/citation namespaces, documented macros, whitespace, comments and
nonsemantic display directives are normalized. Inserted editorial text is retained.
"""
from pathlib import Path, PurePosixPath
import argparse, collections, difflib, hashlib, io, json, re, subprocess, zipfile

SNAPSHOTS = [{'commit': 'c5f6a3219', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/article.tex', 'sha256': 'c0779e7d5ff51efc0b1c290279680688d8f7179223840cdc7f0ca2c65bc34d1a', 'bytes': 411038}, {'commit': 'c5f6a3219', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/README.md', 'sha256': '6c71c6fe63829f88dac2f7ccfc4fa1d6da60a55542785360f3b3a90f9d341494', 'bytes': 32657}, {'commit': 'c5f6a3219^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/article.tex', 'sha256': 'b10a84273a257f3b6c019b3639a4958331ac29a796135b074b836cf9f6f251eb', 'bytes': 307340}, {'commit': 'c5f6a3219^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/README.md', 'sha256': '81f7084e07a6e9acedf3cb721acf51509bdf4772ba229fc753c32ff363525ffc', 'bytes': 21672}, {'commit': 'c03d95fe6', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/polynomial-witness-histories/article.tex', 'sha256': '2f601be5c8cfce4a5fb0ce057c7e9e8579e2859d268cb3fc6e5394fcc8adc385', 'bytes': 288870}, {'commit': 'c03d95fe6', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/polynomial-witness-histories/README.md', 'sha256': '1c5369df44bd856e3f9b30b805cdde21a063c4918f57c39526d8ebb49f28acf9', 'bytes': 27370}, {'commit': 'c03d95fe6^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/polynomial-witness-histories/article.tex', 'sha256': '709bab5303e4cc2f6e14212db2c75f79ee7da92c0ba402076af2cbb2c451fc49', 'bytes': 81579}, {'commit': 'c03d95fe6^', 'path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/polynomial-witness-histories/README.md', 'sha256': '5b07270691b6c41fa2f9decdb8619c72e20b62c554e23c6f13b380ca56e78bf0', 'bytes': 8513}]

ARCHIVES = [{'label': 'clock', 'arrival': '060e08a07', 'archive': 'clock_spectra_research.zip', 'sha256': 'dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22'}, {'label': 'histories', 'arrival': '060e08a07', 'archive': 'unique_polynomial_histories.zip', 'sha256': '0f0f52d5c6617a22cdd0820386eb378c700e5f5c36bfee810ae13818137465e4'}, {'label': 'one_coordinate', 'arrival': 'ef2fc7990', 'archive': 'one_coordinate_certificates.zip', 'sha256': '453ae5f3b3726a288ae30325cbf8e1b6aa15bf6495fb5f23f4e8e8985f713829'}, {'label': 'boundary', 'arrival': '060e08a07', 'archive': 'Linear_Boundary_Transport_Research.zip', 'sha256': '7b2b3505fe36d9f01777bd198742cc1206f1232e0951964d1ee30681c6c5e096'}]

BASE = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/'
CASES = {
 'clock': ('liveness-beyond-halting', 'c5f6a3219', 'clock_spectra_research/article.tex', 'lbh:cs:'),
 'histories': ('polynomial-witness-histories', 'c03d95fe6', 'unique_polynomial_histories/unique_polynomial_histories.tex', 'pwh:uh:'),
 'one_coordinate': ('polynomial-witness-histories', 'c03d95fe6', 'one_coordinate_certificates/one_coordinate_certificates.tex', 'pwh:oc:'),
 'boundary': ('polynomial-witness-histories', 'c03d95fe6', 'linear_boundary_transport/article.tex', 'pwh:bt:'),
}
REVIEWS = [
 ('review_spectral_060e08a07.md','2c311e525'),
 ('review_unique_polynomial_histories.md','e5497072e'),
 ('review_one_coordinate_aebfa.md','a21c86070'),
 ('review_boundary_sandpile_060e08a07.md','49bc4c654'),
]
def require(ok, message):
 if not ok: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def git(repo,*args):
 return subprocess.run(['git','-C',str(repo),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def blob(repo,rev,path): return git(repo,'show',rev+':'+path)
def normalize(t,case):
 t=re.sub(r'(?<!\\)%[^\n]*','',t)
 t=re.sub(r'\\label(?:\[[^]]+\])?\{[^}]+\}','',t)
 t=re.sub(r'(lbh:cs:|pwh:uh:|pwh:oc:|pwh:bt:)','',t)
 def citations(m):
  keys=','.join(re.sub(r'^(cs-|uh:|oc:|bt:)','',k.strip()) for k in m[2].split(','))
  return m[1]+keys+m[3]
 t=re.sub(r'(\\cite(?:\[[^]]*\])?\{)([^}]*)(\})',citations,t)
 if case=='clock':
  for name in ('Clock','Spec','BS','Cone','degT','zero'): t=t.replace('\\cs'+name,'\\'+name)
  t=t.replace('\\secref','\\cref')
 if case=='boundary': t=t.replace('\\Fbb','\\F')
 t=re.sub(r'\\(?:notag|nonumber|displaystyle|textstyle)\b','',t)
 return re.sub(r'\s+','',t)
def envs(t,env):
 e=re.escape(env)
 return re.findall(r'\\begin\{'+e+r'\}(.*?)\\end\{'+e+r'\}',t,re.S)
def displays(t):
 return sum((envs(t,e) for e in ('equation','equation*','align','align*','gather','gather*')),[])+re.findall(r'(?<!\\)\\\[(.*?)\\\]',t,re.S)
def labels(t): return re.findall(r'\\label(?:\[[^]]+\])?\{([^}]+)\}',t)
def edits(a,b):
 return [{'old':a[i:j],'new':b[k:l]} for tag,i,j,k,l in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes() if tag!='equal']
def comparison(old,new,case,prefix):
 full_new=new
 part_label={'clock':'lbh:part:spectra','histories':'pwh:part:uh','one_coordinate':'pwh:part:oc','boundary':'pwh:part:bt'}[case]
 marker=new.index('\\label{'+part_label+'}')
 start=new.rfind('\\part{',0,marker)
 ends=[i for i in (new.find('\\part{',marker),new.find('\\appendix',marker)) if i>=0]
 new=new[start:min(ends)]
 ol=labels(old);nl=labels(new)
 require(all(prefix+x in nl for x in ol),'missing original label')
 require(len(nl)==len(set(nl)),'duplicate label')
 target=collections.Counter(normalize(x,case) for x in displays(new))
 for x in displays(old):
  n=normalize(x,case);require(target[n]>0,'changed or missing original display');target[n]-=1
 stotal=ssame=0;sd=[]
 for env in ('theorem','lemma','proposition','corollary','definition','remark','example','question'):
  nb=envs(new,env)
  for b in envs(old,env):
   ls=labels(b)
   if not ls: continue
   matches=[q for q in nb if prefix+ls[0] in labels(q)]
   require(len(matches)==1,'statement label lost')
   a,c=normalize(b,case),normalize(matches[0],case);stotal+=1
   if a==c:ssame+=1
   else:
    diff=edits(a,c);require(all(x['old']=='' for x in diff),'original statement text altered')
    sd.append({'environment':env,'label':ls[0],'insertions':diff})
 nb=[normalize(x,case) for x in envs(new,'proof')];counts=collections.Counter(nb);psame=0;pd=[]
 for i,b in enumerate(envs(old,'proof')):
  a=normalize(b,case)
  if counts[a]:psame+=1;counts[a]-=1;continue
  c=max(nb,key=lambda q:difflib.SequenceMatcher(None,a,q,autojunk=False).ratio())
  diff=edits(a,c);require(all(x['old']=='' for x in diff),'original proof text altered')
  pd.append({'source_proof_index':i,'insertions':diff})
 pat=r'\\(?:newcommand|renewcommand)\*?(?:\{(\\\w+)\}|(\\\w+))([^\n]*)'
 nm={a or b:re.sub(r'\s+','',v) for a,b,v in re.findall(pat,full_new)};macros=[]
 for a,b,v in re.findall(pat,old):
  a=a or b
  if a in ('\\headrulewidth','\\repo','\\code','\\codename','\\secref'):continue
  target='\\cs'+a[1:] if case=='clock' and a[1:] in ('Clock','Spec','BS','Cone','degT','zero') else ('\\Fbb' if case=='boundary' and a=='\\F' else a)
  require(nm.get(target)==re.sub(r'\s+','',v),'mathematical macro changed: '+a);macros.append([a,target])
 return {'original_labels':len(ol),'all_original_labels_present':True,'target_part_labels':len(nl),'matching_restricted_to_corresponding_part':True,
  'original_display_blocks':len(displays(old)),'exact_normalized_displays':len(displays(old)),
  'labelled_statements':stotal,'exact_normalized_statements':ssame,'statement_insertions':sd,
  'original_proofs':len(envs(old,'proof')),'exact_normalized_proofs':psame,'proof_insertions':pd,
  'mathematical_macro_definitions_preserved':macros}
def placed(case,name):
 # Only renamed delivery members; original articles, READMEs/PDFs and manifests excluded.
 rel='/'.join(PurePosixPath(name).parts[1:]);p=PurePosixPath(rel)
 if case=='clock':
  if rel.startswith('code/') or rel=='build.sh':return 'code/12-clock-spectra-'+p.name
  if rel.startswith('examples/') or rel=='test_results.json':return 'data/12-clock-spectra-'+p.name
  if rel=='source_audit.md':return '12-clock-spectra-source_audit.md'
 if case=='histories':
  if rel.startswith('code/'):return 'code/06-polynomial-histories-'+p.name
  if rel.startswith('results/') and p.name not in ('example_binary_quadratic.json','example_weighted_quadratic.json'):return 'data/06-polynomial-histories-'+p.name
 if case=='one_coordinate':
  if rel.startswith('code/'):return 'code/15-one-coordinate-'+p.name
  if rel.startswith('results/') and p.name!='example_quartic.json':return 'data/15-one-coordinate-'+p.name
 if case=='boundary':
  if rel.startswith('code/') or rel=='Makefile':return 'code/01-boundary-transport-'+p.name
  if rel.startswith('examples/') or rel.startswith('validation/'):return 'data/01-boundary-transport-'+p.name
  if rel=='SOURCE_AUDIT.md':return '01-boundary-transport-SOURCE_AUDIT.md'
 return None

def verify(repo):
 repo=Path(repo);snaps={};out={'status':'PASS','snapshots':[], 'commit_changes':[], 'archives':[], 'comparisons':{},'prior_review_pins':[]}
 for spec in SNAPSHOTS:
  data=blob(repo,spec['commit'],spec['path']);require(sha(data)==spec['sha256'] and len(data)==spec['bytes'],'snapshot pin mismatch')
  snaps[(spec['commit'],spec['path'])]=data.decode();out['snapshots'].append(dict(spec))
 for rev,folder in (('c5f6a3219','liveness-beyond-halting'),('c03d95fe6','polynomial-witness-histories')):
  changed=git(repo,'diff-tree','--no-commit-id','--name-only','-r',rev).decode().splitlines()
  require(set(changed)=={BASE+folder+'/'+n for n in ('article.tex','article.pdf','README.md')},'unexpected code or other change')
  out['commit_changes'].append({'commit':git(repo,'rev-parse',rev).decode().strip(),'parent':git(repo,'rev-parse',rev+'^').decode().strip(),
   'files':[{'path':p,'sha256':sha(blob(repo,rev,p)),'bytes':len(blob(repo,rev,p))} for p in changed]})
 for spec in ARCHIVES:
  case=spec['label'];folder,rev,article,prefix=CASES[case]
  data=blob(repo,spec['arrival'],'docs/incoming/'+spec['archive']);require(sha(data)==spec['sha256'],'archive pin mismatch')
  members={};records=[];mapped=[]
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   for info in z.infolist():
    if info.is_dir():continue
    p=PurePosixPath(info.filename)
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename and info.filename not in members,'unsafe or duplicate member')
    require((info.external_attr>>16)&0o170000 != 0o120000,'symlink member')
    b=z.read(info);members[info.filename]=b;records.append({'path':info.filename,'sha256':sha(b),'bytes':len(b)})
    target=placed(case,info.filename)
    if target:
     bp=blob(repo,rev,BASE+folder+'/'+target);require(bp==b,'delivery bytes differ: '+target)
     mapped.append({'member':info.filename,'placed_path':BASE+folder+'/'+target,'sha256':sha(b)})
  out['archives'].append({**spec,'members':records,'identical_placed_members':mapped})
  out['comparisons'][case]=comparison(members[article].decode(),snaps[(rev,BASE+folder+'/article.tex')],case,prefix)
 for name,rev in REVIEWS:
  p='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'+name;b=blob(repo,rev,p)
  out['prior_review_pins'].append({'commit':rev,'path':p,'sha256':sha(b),'bytes':len(b)})
 out['scope']={'author_code_executed':False,'pdf_rebuilt_or_visual_layout_audited':False,
  'normalization_is_not_a_proof_checker':True,'future_revisions_covered':False,
  'editorial_claims_require_companion_human_review':True}
 out['totals']={k:sum(v[k] for v in out['comparisons'].values()) for k in ('original_labels','original_display_blocks','exact_normalized_displays','labelled_statements','exact_normalized_statements','original_proofs','exact_normalized_proofs')}
 out['totals']['preserved_mathematical_macro_definitions']=sum(len(v['mathematical_macro_definitions_preserved']) for v in out['comparisons'].values())
 out['totals']['original_archive_members']=sum(len(v['members']) for v in out['archives'])
 out['totals']['byte_identical_placed_members']=sum(len(v['identical_placed_members']) for v in out['archives'])
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path.cwd());ap.add_argument('--receipt',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--write',action='store_true');args=ap.parse_args()
 result=verify(args.repo);encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if args.write:args.receipt.write_text(encoded)
 else:require(exact(result,json.loads(args.receipt.read_text())),'saved receipt mismatch')
 print(json.dumps({'status':'PASS','counts':result['totals']},sort_keys=True))
if __name__=='__main__':main()
