#!/usr/bin/env python3
"""Fresh immutable publication metadata/body checker; supplied programs stay inert.
No mathematical proof, PDF build, archived program, or previous review is executed.
All transformations are declared below; substantive edits remain explicit.
"""
import argparse,collections,hashlib,io,json,re,subprocess,zipfile
from pathlib import Path
COMMIT='a21208b3ff14a07a4c8318dbf916d543acbef043'
PARENT='52a34387969be9cf56e36c1c9241e0eb1407a72c'
ARRIVAL='26e036956381b07bb43de0187965f8dcdf9194fb'
HOST='SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games/'
ZIPPATH='docs/incoming/hat_randomness_frontier.zip'
MEMBER='hat_randomness_frontier/hat_randomness_frontier.tex'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(root,*args):return subprocess.check_output(['git','-C',str(root),*args])
def blob(root,c,p):return git(root,'show',c+':'+p)
def pin(root,c,p):
 b=blob(root,c,p)
 return {'commit':c,'path':p,'blob':git(root,'rev-parse',c+':'+p).decode().strip(),'bytes':len(b),'sha256':sha(b)}
def span(b,a,z):
 lines=b.splitlines(keepends=True);require(1<=a<=z<=len(lines),'span')
 return {'start_line':a,'end_line':z,'sha256':sha(b''.join(lines[a-1:z]))}
def labels(s):return re.findall(r'\\label\{([^}]+)\}',s)
def stripnotes(s):
 s=re.sub(r'\\begin\{writenote\}.*?\\end\{writenote\}','',s,flags=re.S)
 s=re.sub(r'^%.*$','',s,flags=re.M)
 return s

def balanced(s,p):
 assert s[p]=='{'; start=p;level=0
 for p in range(p,len(s)):
  if s[p]=='{':level+=1
  if s[p]=='}':
   level-=1
   if level==0:return s[start+1:p],p+1
 raise ValueError('brace')

def norm(s):
 s=stripnotes(s).replace('mbg:rnd:','')
 s=re.sub(r'\\label\{[^}]+\}','',s)
 for a,b in [(r'\Theta','T'),(r'\vartheta',r'\alpha'),(r'\kappa','K'),(r'\zeta','K'),(r'\bar q_n','B_n'),(r'\nu','m'),(r'\ind',r'\one'),('hat:Eldredge','Eldredge'),('rnd:ProveIt','ProveIt'),('rnd:Beckner','Beckner'),('GlazerBox','Glazer')]:s=s.replace(a,b)
 s=s.replace(r'\as','almost surely').replace(r'\text{almost surely}','almost surely')
 s=re.sub(r'\\norm\s*([A-Za-z])\s*(\{[^}]+\}|[0-9])',lambda m:'NORM('+m[1]+','+m[2].strip('{}')+')',s)
 # Remove formatting distinctions in the same referenced statement.
 s=re.sub(r'(?:(?:Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Sections?|Remarks?|Research questions?)~)?\\(?:[cC]ref|ref)\{([^}]+)\}',lambda m:' REF('+m[1]+') ',s)
 s=re.sub(r'REF\(([^)]+)\)\s+and~?\s*REF\(([^)]+)\)',r'REF(\1,\2)',s)
 # Norm two-arg macro and old/new subscripts.
 p=0
 while True:
  k=s.find(r'\norm{',p)
  if k<0:break
  x,j=balanced(s,k+5)
  if j<len(s) and s[j]=='{': y,end=balanced(s,j)
  elif j<len(s) and s[j]=='_':
   if s[j+1]=='{':y,end=balanced(s,j+1)
   else:y,end=s[j+1],j+2
  else:p=j;continue
  s=s[:k]+'NORM('+x+','+y+')'+s[end:];p=k+5
 return re.sub(r'\s+','',s)

def blocks(s):
 s=stripnotes(s);out={}
 pat=r'\\begin\{(theorem|lemma|proposition|corollary|definition|remark|question)\}(?:\[([^\n]*)\])?'
 for m in re.finditer(pat,s):
  typ,title=m[1],m[2] or '';end=s.index('\\end{'+typ+'}',m.end())+len('\\end{'+typ+'}')
  body=s[m.start():end];labs=re.findall(r'\\label\{([^}]+)\}',body)
  key=labs[0].replace('mbg:rnd:','') if labs else title
  if key=='def:randomness':key='Private and public randomness'
  tail=s[end:].lstrip();proof=''
  if tail.startswith(r'\begin{proof}'):
   proof=tail[:tail.index(r'\end{proof}')+len(r'\end{proof}')]
  out[key]={'statement':body,'proof':proof}
 return out
def body(s,isnew,B):
 s=stripnotes(s)
 if isnew:
  a=s.index(r'\subsection{Provenance and place in this report}')
  b=s.index(r'\section{Model, legal algorithms, and notation}',a)
  s=s[:a]+s[b:]
  for key in ['rem:finite-valued','cor:prescribed','cor:conditional','q:heuristic','q:measure','q:review']:
   b=B[key];s=s.replace(b['statement'],'').replace(b['proof'],'') if b['proof'] else s.replace(b['statement'],'')
  s=s.replace(r'\subsection*{Further questions and research: claims stated without proof}','')
  while r'{\small\textbf{[write]}' in s:
   a=s.index(r'{\small\textbf{[write]}');_,b=balanced(s,a);s=s[:a]+s[b:]
  s=re.sub(r'^\\(?:setcounter|renewcommand|makeatletter|clearpage|fancyhead).*$', '',s,flags=re.M)
 else:s=s.replace(r'\appendix','')
 s=s[s.index(r'\section{Research intersection and principal results}'):]
 s=s.split(r'\begin{thebibliography}')[0]
 return norm(s)

def build(root,correction):
 result={'schema':'hat-write-publication-review-v1','source_sha256':sha(Path(__file__).read_bytes()),'commit':COMMIT,'parent':PARENT,
 'scope':'Immutable metadata and normalized textual preservation; targeted proof challenge; no archived/predecessor program execution or PDF read/build.'}
 require(git(root,'rev-parse',COMMIT+'^').decode().strip()==PARENT,'parent')
 paths=git(root,'diff','--name-only',PARENT,COMMIT).decode().splitlines()
 require(set(paths)=={HOST+x for x in ['README.md','article.tex','article.pdf']},'changed paths')
 files=[]
 for p in paths:
  a,b=blob(root,PARENT,p),blob(root,COMMIT,p)
  r={'path':p,'before':pin(root,PARENT,p),'after':pin(root,COMMIT,p)}
  if not p.endswith('.pdf'):
   d=git(root,'diff','--no-ext-diff','--no-textconv',PARENT,COMMIT,'--',p)
   r['raw_diff']={'sha256':sha(d),'bytes':len(d),'lines':len(d.splitlines())}
   r['diff_read_scope']='Full raw guide diff' if p.endswith('README.md') else 'Hunks 1-180 and 1780-1911 read; new editorial notes and selected proof spans read separately; entire body mechanically reconciled.'
   if p.endswith('README.md'):r['raw_diff']['read_spans']=[span(d,1,len(d.splitlines()))]
   else:r['raw_diff']['read_spans']=[span(d,1,180),span(d,1780,1911)]
  files.append(r)
 result['files']=files
 cm=git(root,'show','--no-patch','--format=%B',COMMIT)
 result['commit_message']={'sha256':sha(cm),'bytes':len(cm),'read_spans':[span(cm,1,len(cm.splitlines()))]}
 zb=blob(root,ARRIVAL,ZIPPATH)
 require(sha(zb)=='eccc49ac838592997e1c7d8ef0c5ba7c1a95bd76abbb8f12814f552dc34b9e20','archive pin')
 z=zipfile.ZipFile(io.BytesIO(zb));members=[]
 for n in z.namelist():
  if not n.endswith('/'):
   b=z.read(n);members.append({'path':n,'bytes':len(b),'sha256':sha(b),'coverage':'inert bytes; manuscript comparison when named below'})
 require(len(members)==8,'member census')
 result['archive']={**pin(root,ARRIVAL,ZIPPATH),'members':members,'internal_checksum_manifest':False}
 ob=z.read(MEMBER);old=ob.decode();require(sha(ob)=='7d6c4815a4be0363a6d0deee1189396b4818033102ee28b21eb04b8102b47c71','tex pin')
 before=blob(root,PARENT,HOST+'article.tex').decode();afterb=blob(root,COMMIT,HOST+'article.tex');after=afterb.decode()
 new=after.split(r'\label{mbg:rnd:part}',1)[1].split(r'\begin{thebibliography}',1)[0]
 A,B=blocks(old),blocks(new);rows=[]
 for k,a in A.items():
  require(k in B,'missing source block '+k);b=B[k]
  r={'key':k,'statement_normalized_equal':norm(a['statement'])==norm(b['statement']),
     'proof_normalized_equal':norm(a['proof'])==norm(b['proof']),'has_proof':bool(a['proof']),
     'old_statement_sha256':sha(a['statement'].encode()),'new_statement_sha256':sha(b['statement'].encode()),
     'old_proof_normalized_sha256':sha(norm(a['proof']).encode()),'new_proof_normalized_sha256':sha(norm(b['proof']).encode())}
  require(r['proof_normalized_equal'],'proof mutation '+k)
  require(r['statement_normalized_equal'] or k in ['Private and public randomness','thm:finite-public'],'unexpected statement '+k)
  rows.append(r)
 require(len(A)==42 and len(B)==48,'statement census')
 # For the full main-body comparison, permit only the two explicit W1 repairs,
 # two retained/reclassified sentences, editorial notes/layout, and printed renamings.
 old_patched=old
 for k in ['Private and public randomness','thm:finite-public']:
  require(old_patched.count(A[k]['statement'])==1,'repair target uniqueness')
  old_patched=old_patched.replace(A[k]['statement'],B[k]['statement'])
 x,y=body(old_patched,False,B),body(new,True,B)
 moved=['Afinite-prefixprobabilityestimatealonewouldnotsettlethatissue.',
        'Thepivotalproofstepsandtheendpointconstructionswerealsoindependentlyreviewedduringpreparation.']
 for phrase in moved:
  require(x.count(phrase)==1,'moved text exact occurrence');x=x.replace(phrase,'')
 require(x==y,'full normalized main-body residual')
 # All 38 labeled equations are compared independently, without W1 overrides.
 equations=[]
 for m in re.finditer(r'\\begin\{(equation|align)\}.*?\\end\{\1\}',old,re.S):
  for key in labels(m[0]):
   matches=[n[0] for n in re.finditer(r'\\begin\{(equation|align)\}.*?\\end\{\1\}',new,re.S) if 'mbg:rnd:'+key in labels(n[0])]
   require(len(matches)==1 and norm(m[0])==norm(matches[0]),'equation '+key)
   equations.append({'label':key,'normalized_sha256':sha(norm(m[0]).encode())})
 require(len(equations)==38,'equation census')
 src_labs=labels(old);pre_labs=labels(before);post_labs=labels(after)
 require(len(src_labs)==80 and len(pre_labs)==335 and len(post_labs)==427,'labels census')
 require(len(set(post_labs))==427,'duplicate labels')
 require(set(pre_labs)<=set(post_labs),'old label loss')
 require({'mbg:rnd:'+x for x in src_labs}<=set(post_labs),'delivered label loss')
 refs=re.findall(r'\\(?:[cC]?ref|eqref|pageref|autoref)\{([^}]+)\}',after)
 missing=sorted({x.strip() for r in refs for x in r.split(',') if x.strip() not in set(post_labs)})
 require(not missing,'unresolved simple refs')
 result['normalized_body']={'whole_main_body_equal_under_declared_edits':True,'normalized_sha256':sha(x.encode()),'normalized_characters':len(x),
 'statement_and_proof_rows':rows,'equations':equations,'source_label_map':[{'old':a,'new':'mbg:rnd:'+a} for a in src_labs],
 'added_labels':sorted(set(post_labs)-set(pre_labs)-{'mbg:rnd:'+x for x in src_labs}),
 'old_host_labels':335,'new_host_labels':427,'unresolved_simple_refs':missing,
 'normalization_scope':'Main body from source section1 through appendixB, excluding bibliography, source preamble/abstract, added editorial notes/provenance/notation and six added named environments. Same five letter renamings, reference kinds/prefixes, norm macro, indicator/as typography and appendix layout. Only W1 definition/theorem replacements and two retained moved sentences are substantive main-body exceptions. All original proofs separately equal.'}
 # Archive ancillary identity at both publication endpoints.
 suffixes={'verify_finite.py':'code/06-hat-randomness-verify_finite.py','results.json':'data/06-hat-randomness-results.json','VERIFY_NOTES.txt':'code/06-hat-randomness-VERIFY_NOTES.txt','SOURCE_AUDIT.txt':'06-hat-randomness-SOURCE_AUDIT.txt','Makefile':'code/06-hat-randomness-Makefile'}
 placements=[]
 for member,p in suffixes.items():
  n='hat_randomness_frontier/'+member;p=HOST+p;b=z.read(n)
  require(blob(root,PARENT,p)==b and blob(root,COMMIT,p)==b,'ancillary equality '+p)
  placements.append({'archive_member':n,'path':p,'sha256':sha(b),'before':pin(root,PARENT,p),'after':pin(root,COMMIT,p),'coverage':'inert byte equality only; no program execution or test replay'})
 result['ancillary_placements']=placements
 # Explicit human read evidence. Bytes of each line span include existing line endings.
 spans=[(7934,8240),(8290,8305),(8540,8592),(8600,8890),(8925,8940),(9015,9029),(9058,9070),(9290,9375),(9400,9450),(9465,9705),(9958,9986)]
 result['human_reads']={'article':{**pin(root,COMMIT,HOST+'article.tex'),'spans':[span(afterb,a,b) for a,b in spans]},
 'original_manuscript':{'archive_member':MEMBER,'sha256':sha(ob),'new_read_spans':[span(ob,1,110)],'inherited_scope':'See the pinned correction and earlier reviews; machine normalization reads the full member without certifying the full proof.'},
 'guide':{**pin(root,COMMIT,HOST+'README.md'),'specific_finding_span':span(blob(root,COMMIT,HOST+'README.md'),680,709)}}
 deps=[]
 for name in ['review_new_actions_26e036956.md','review_hat_endpoint_26e036956.md','review_hat_placement_635a3e026.md']:
  deps.append(pin(root,COMMIT,WIP+name))
 cb=Path(correction).read_bytes();require(sha(cb)=='91323ce99a38e5b6951eb5940ccbba034a658259c07fcb61c8c658d5320a9701','correction note')
 result['prior_reviews']=deps
 result['correction_review']={'basename':Path(correction).name,'bytes':len(cb),'sha256':sha(cb),'coverage':'full proof-note read, no code'}
 # Exact numerical witnesses to the two new errors, independent of any supplied test.
 from fractions import Fraction as F
 eps=F(1,10000);private_cap=F(19999,19998);success=1-eps
 require(1<private_cap<1/success and success*private_cap<1 and success>1-F(1,5184),'gap witness')
 result['fresh_counterexample_arithmetic']={'public_gate_probability':str(success),'permitted_private_cap':str(private_cap),'unconditional_cap_upper':str(success*private_cap),'private_gap':str(1-F(1,5184)),
 'collision_example':{'law':'half mass at the atom 1, half uniform on (2,3)','diffuse_mass':'1/2','first_diffuse_bin_mass':'1/4','actual_probability_of_g_1':'3/4','false_claimed_probability':'1/4'}}
 result['findings']=[{'id':'F1','severity':'guide false uniform gap','location':'README.md:685-688','refutation':'Prop79.3 two-valued mixture with epsilon=1/10000 exceeds the private bound at unconditional cap below1.'},{'id':'F2','severity':'minor proof equality error; theorem survives','location':'article.tex:8820','refutation':'An atomic output equal to integer j adds mass; replace = by >= or tag the codomain.'}]
 result['not_performed']=['No supplied, archived, committed, frozen or predecessor helper execution/import','No tests reproduced from saved evidence','No TeX/PDF build or rendered-PDF inspection','No external source/novelty audit','No fresh full proof certification of unchanged source']
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--correction',default='/tmp/review_hat_seed_definition_correction.md');g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--check');args=ap.parse_args()
 raw=(json.dumps(build(Path(args.root),args.correction),sort_keys=True,indent=2)+'\n').encode()
 if args.output:
  with open(args.output,'xb') as f:f.write(raw)
 else:require(Path(args.check).read_bytes()==raw,'receipt differs')
 print('PASS: immutable source/body/labels/placements and two retained findings')
if __name__=='__main__':main()
