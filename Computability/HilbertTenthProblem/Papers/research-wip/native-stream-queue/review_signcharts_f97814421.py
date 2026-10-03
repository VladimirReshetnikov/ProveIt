#!/usr/bin/env python3
"""Read-only semantic-transfer checks at one fixed integration commit.
No source module is imported, test suite replayed, or LaTeX build run.
"""
import argparse
from collections import Counter, defaultdict, deque
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

COMMIT='f97814421444abae15b469eb30c7343d03c65394'
ARRIVAL='060e08a07'
REPORT='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
SOURCES={
 'positive': {'archive':'Positive_Spectrum_Diophantine.zip','sha256':'fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8','article':'Positive_Spectrum_Diophantine/article.tex','article_sha256':'ffe039f42d006c97010b0ce626b67c8cd377225b3112f6311e9d95be7c9a19ba','prefix':'cdc:ps:','stem':'17-positive-spectrum-','count':46,'cites':{'repo-canonical':'repo-cdc','matiyasevich':'mat-scholarpedia','hfg':'hfg2024','how':'how2019','cow':'cow2023'}},
 'spectral': {'archive':'Spectral_Guards_Without_Time_Expansion.zip','sha256':'0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53','article':'Spectral_Guards/article.tex','article_sha256':'66800a6a5bc739300d263fa14481e45fc250327c8418b5d179e439be09ed4c37','prefix':'cdc:sg:','stem':'18-spectral-guards-','count':33,'cites':{'RepoLean':'repo-trace','RepoCertificates':'repo-cdc','LF':'lf2022','HFG':'hfg2024','CCO':'cco2024','Mat':'mat2010','FGGL':'fggl2026','Survey':'bkl-survey'}},
}


def need(ok,message):
 if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args],timeout=60)
def blob(repo,commit,path):return git(repo,'show',commit+':'+path)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def remove_command(text,command):
 pattern=re.compile(r'\\'+re.escape(command)+r'\{')
 out=[];at=0
 while match:=pattern.search(text,at):
  out.append(text[at:match.start()]);i=match.end();depth=1
  while depth:
   need(i<len(text),'unbalanced '+command)
   if text[i]=='{' and text[i-1]!='\\':depth+=1
   if text[i]=='}' and text[i-1]!='\\':depth-=1
   i+=1
  at=i
 out.append(text[at:]);return ''.join(out)

def normal(text,cites=None):
 text=re.sub(r'(?<!\\)%[^\n]*','',text)
 for command in ('label','srctag','srcnote'):text=remove_command(text,command)
 text=re.sub(r'cdc:(ps|sg):','',text)
 if cites:
  text=re.sub(r'(\\cite(?:\[[^\]]*\])?\{)([^}]*)(\})',lambda m:m[1]+','.join(cites.get(k,k) for k in m[2].split(','))+m[3],text)
 text=text.replace(r'\pathcode',r'\code')
 return re.sub(r'\s+','',text)

FORMAL=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition|proof)\}[\s\S]*?\\end\{\1\}')
DISPLAY=re.compile(r'(?<!\\)\\\[[\s\S]*?(?<!\\)\\\]|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}[\s\S]*?\\end\{\1\}')

def labels(text):
 return re.findall(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',re.sub(r'(?<!\\)%[^\n]*','',text))

def verify(repo):
 need(__debug__,'run without -O')
 repo=Path(repo).resolve();article_b=blob(repo,COMMIT,REPORT+'/article.tex');article=article_b.decode()
 readme_b=blob(repo,COMMIT,REPORT+'/README.md');readme=readme_b.decode()
 previous=blob(repo,COMMIT+'^',REPORT+'/article.tex').decode()
 old_labels,new_labels=labels(previous),labels(article)
 need(len(old_labels)==len(set(old_labels))==1179,'parent label census')
 need(len(new_labels)==len(set(new_labels))==1322,'target label census')
 need(set(old_labels)<=set(new_labels),'old labels removed')
 normalized_main=normal(article)
 math_target=defaultdict(deque)
 for m in DISPLAY.finditer(article):math_target[normal(m.group())].append(m)
 package_results={};mapped=[]
 starts={'positive':article.index(r'\section{Definitions and arithmetic conventions\srctag{17}}'), 'spectral':article.index(r'\section{Data, domains, and representation conventions\srctag{18}}')}
 ends={'positive':starts['spectral'],'spectral':article.index(r'\section{Two routes to one theorem}')}
 for kind,spec in SOURCES.items():
  archive=blob(repo,ARRIVAL,'docs/incoming/'+spec['archive']);need(sha(archive)==spec['sha256'],'archive pin '+kind)
  with zipfile.ZipFile(io.BytesIO(archive)) as z:
   members=z.namelist();need(len(members)==len(set(members)),'duplicate archive names')
   for entry in z.infolist():
    p=PurePosixPath(entry.filename)
    need(not p.is_absolute() and '..' not in p.parts and '\\' not in entry.filename and ((entry.external_attr>>16)&0o170000)!=0o120000,'unsafe archive member')
   source_b=z.read(spec['article']);need(sha(source_b)==spec['article_sha256'],'article pin '+kind);source=source_b.decode()
   fragment=article[starts[kind]:ends[kind]]
   target=defaultdict(deque)
   for m in FORMAL.finditer(fragment):target[normal(m.group())].append(m)
   formal=[]
   for m in FORMAL.finditer(source):
    normalized=normal(m.group(),spec['cites']);need(bool(target[normalized]),'changed or missing formal occurrence '+kind+':'+str(source[:m.start()].count('\n')+1))
    found=target[normalized].popleft()
    formal.append({'environment':m[1],'source_line':source[:m.start()].count('\n')+1,'target_line':article[:starts[kind]+found.start()].count('\n')+1,'source_labels':labels(m.group()),'normalized_sha256':sha(normalized.encode())})
   need(len(formal)==spec['count'],'formal block count')
   source_labels=labels(source);missing=[label for label in source_labels if spec['prefix']+label not in new_labels]
   need(not missing,'missing source labels')
   body_start=source.index(r'\begin{document}')+len(r'\begin{document}')
   body=source[body_start:].split(r'\begin{thebibliography}',1)[0]
   displays=[]
   for m in DISPLAY.finditer(body):
    normalized=normal(m.group(),spec['cites']);need(bool(math_target[normalized]),'changed or missing display occurrence '+kind+':'+normalized)
    found=math_target[normalized].popleft()
    displays.append({'source_line':source[:body_start+m.start()].count('\n')+1,'target_line':article[:found.start()].count('\n')+1,'normalized_sha256':sha(normalized.encode())})
   root=PurePosixPath(spec['article']).parent
   for member in members:
    if member.endswith('/'):continue
    rel=str(PurePosixPath(member).relative_to(root))
    if rel in ('article.tex','article.pdf','README.md','SHA256SUMS.txt','data/test_log.txt','validation/test_output.txt'):continue
    parts=PurePosixPath(rel).parts
    if rel=='Makefile':dest='code/'+spec['stem']+'Makefile'
    elif parts[0]=='code':dest='code/'+spec['stem']+parts[-1]
    elif parts[0] in ('data','examples','validation'):dest='data/'+spec['stem']+parts[-1]
    else:dest=spec['stem']+parts[-1]
    original=z.read(member);placed=blob(repo,COMMIT,REPORT+'/'+dest)
    need(original==placed,'placed file differs '+dest)
    mapped.append({'source_member':member,'target_path':REPORT+'/'+dest,'bytes':len(original),'sha256':sha(original)})
  need(all(r'\bibitem{'+dest+'}' in article for dest in spec['cites'].values()),'citation target missing')
  package_results[kind]={'archive':spec['archive'],'archive_sha256':spec['sha256'],'article_member':spec['article'],'article_sha256':spec['article_sha256'],'source_labels_preserved':len(source_labels),'formal_environment_counts':dict(Counter(x['environment'] for x in formal)),'formal_environment_total':len(formal),'formal_blocks':formal,'display_formulas_preserved':len(displays),'display_formula_occurrences':displays,'citation_key_map':spec['cites']}
 need(len(mapped)==29,'placed package count')
 # Every reference in the added core resolves to a declared label at this commit.
 part=article[article.index(r'\part{Exponential trajectories:'):article.index(r'\section{Theorem and implementation ledger\srctag{18}}')]
 refs=[]
 for m in re.finditer(r'\\(?:c|C|eq)?ref\{([^}]+)\}',part):refs.extend(m[1].split(','))
 need(all(x in new_labels for x in refs),'dangling new-core reference')
 # Confirm the preexisting Lean declarations cited by the editorial comparison.
 lean=[]
 for rel in ('Computability/HilbertTenthProblem/Lean/Diophantine/Paper1984/DPR.lean','Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean'):
  now=blob(repo,COMMIT,rel);old=blob(repo,'e58b724c25bd34533b7a5834cfcbe873dfa01288',rel)
  need(now==old,'cited Lean source changed')
  lean.append({'path':rel,'sha256':sha(now),'unchanged_since_source_pin':True})
 # These records support scope comparison only; none is imported or executed.
 research={}
 for name in ('review_spectral_060e08a07.md','review_spectral_060e08a07.py','review_spectral_060e08a07.json','presburger_congruence_five.md','presburger_congruence_five.py','presburger_congruence_five.json','review_presburger_congruence_five.md','review_presburger_congruence_five.py','review_presburger_congruence_five.json'):
  data=blob(repo,COMMIT,WIP+'/'+name);research[name]={'git_blob':git(repo,'rev-parse',COMMIT+':'+WIP+'/'+name).decode().strip(),'sha256':sha(data),'bytes':len(data)}
 need(research['presburger_congruence_five.py']['sha256']=='f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc','Presburger source differs from its independent review')
 for name in ('positive_boundaries.patch','spectral_boundaries.patch'):
  data=blob(repo,COMMIT,WIP+'/spectral_repairs_060e08a07/'+name);research[name]={'sha256':sha(data),'bytes':len(data)}
 # Count the shipped interface arrays directly; do not execute their verifiers.
 exports={}
 for mode in ('finite','infinite'):
  path=REPORT+'/data/17-positive-spectrum-'+mode+'_certificate.json'
  data=json.loads(blob(repo,COMMIT,path))
  inputs=sum(v['role']=='input' for v in data['variables'])
  counts={'inputs':inputs,'witnesses':len(data['variables'])-inputs,'residuals':len(data['quadratic_residuals']),'power_atoms':len(data['power_atoms']),'expanded_monomials':len(data['expanded_quartic'])}
  expected={'finite':(7,1231,1703,52,7502),'infinite':(6,1297,1767,52,8256)}[mode]
  need(tuple(counts.values())==expected,'positive displayed export counts')
  exports['positive_'+mode]=counts
 for mode in ('quasi','quartic'):
  path=REPORT+'/data/18-spectral-guards-hidden_negative_'+mode+'.json'
  data=json.loads(blob(repo,COMMIT,path))
  counts={'inputs':len(data['inputs']),'witnesses':len(data['names'])-len(data['inputs']),'residuals':len(data['residuals']),'power_atoms':len(data['power_atoms'])}
  need(tuple(counts.values())=={'quasi':(10,1294,1212,104),'quartic':(10,1935,1995,0)}[mode],'spectral displayed export counts')
  exports['spectral_'+mode]=counts
 # Guard the precise caveats used in the semantic review; these are not proofs.
 required={'power_atoms_retained':r'The power atoms are retained as separate conjuncts.', 'external_bit_width':r'Fix $B\ge1$ as part of the representation', 'fixed_phase_counts':r'with the counts existentially quantified, uniqueness can fail', 'two_point_disclosure':'a comparison at two points is not a polynomial-identity check', 'unapplied_repairs':'Neither patch is applied to the shipped programs.', 'input_base_cubic_not_claimed':r'neither manuscript proves an $O(D^3)$ bound'}
 for name,text in required.items():need(text in article,'missing reviewed scope text: '+name)
 return {'status':'PASS_BOUNDED_SIGNCHART_TRANSFER','commit':COMMIT,'arrival_commit':git(repo,'rev-parse',ARRIVAL).decode().strip(),'helper_sha256':sha(Path(__file__).read_bytes()),'article_sha256':sha(article_b),'readme_sha256':sha(readme_b),'packages':package_results,'label_census':{'old':len(old_labels),'new':len(new_labels),'source_added':sum(x['source_labels_preserved'] for x in package_results.values()),'editorial_added':len(set(new_labels)-set(old_labels))-sum(x['source_labels_preserved'] for x in package_results.values()),'new_core_reference_occurrences_checked':len(refs)},'placed_files_byte_identical':mapped,'lean_context':lean,'pinned_research_context':research,'required_scope_text':required,'shipped_export_interface_counts':exports,'normalization':'Remove comments, whitespace, label commands, source/editorial wrappers; strip only cdc:ps:/cdc:sg: prefixes; rename citation keys by the explicit maps and pathcode to code. No formula, hypothesis, conclusion or proof clause is deleted. Every formal occurrence consumes a distinct matching target occurrence within its own manuscript core. Each display occurrence consumes a distinct target occurrence in the full integrated text, including introductions and appendices; this target pool is shared across both source manuscripts. Source and target lines are recorded for all matched occurrences.','limits':'Semantic transfer and bounded editorial audit only. No author suite, arithmetic compiler, Lean build, LaTeX build or PDF layout replay. No whole-old-collection proof audit, new primary-literature priority review, future-commit audit, or universal operation improvement.'}


def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',required=True,type=Path);p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.repo)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'receipt mismatch')
 a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':out['status'],'formal_blocks':sum(v['formal_environment_total'] for v in out['packages'].values()),'display_formulas':sum(v['display_formulas_preserved'] for v in out['packages'].values()),'placed_files':len(out['placed_files_byte_identical'])},sort_keys=True))
if __name__=='__main__':main()
