#!/usr/bin/env python3
"""Fresh immutable ZIP/read-span metadata and independent finite algebra checks.
No delivered program is executed or imported; zip members are inert bytes/data.
"""
import argparse,hashlib,io,itertools,json,math,re,subprocess,zipfile
from fractions import Fraction
from pathlib import Path
REPO=Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT='26e036956'
PINNED='715a716a3002b1e9f28daa2d81c009a392851b94'
SPECS={
 'atom_actions_research':{'root':'atom_actions','tex':'atom_actions.tex','reads':{'README.txt':[(1,None)],'SHA256SUMS.txt':[(1,None)],'atom_actions.tex':[(60,677),(907,998),(1212,1260),(1315,1487),(1635,1730)]}},
 'commuting_injections_research':{'root':'commuting_injections','tex':'commuting_injections.tex','reads':{'README.txt':[(1,None)],'commuting_injections.tex':[(1,None)]}},
 'hat_randomness_frontier':{'root':'hat_randomness_frontier','tex':'hat_randomness_frontier.tex','reads':{'README.txt':[(1,None)],'VERIFY_NOTES.txt':[(1,None)],'SOURCE_AUDIT.txt':[(1,None)],'hat_randomness_frontier.tex':[(104,262),(681,822),(1039,1477)]}}
}
CONTEXT=[(COMMIT,'docs/incoming/README.md',[(390,452)],'incoming retention and workflow; task forbids supplied execution/builds'),
 (PINNED,'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/article.tex',[(2240,2277)],'named questions and exact presentation scope'),
 (PINNED,'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games/article.tex',[(5608,5638),(7783,7805)],'randomness questions and resource distinctions')]
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
def spans(raw,rs):
 lines=raw.decode('utf-8').splitlines();out=[]
 for a,b in rs:
  b=len(lines) if b is None else b;need(1<=a<=b<=len(lines),'read span bounds')
  span=('\n'.join(lines[a-1:b])+'\n').encode()
  out.append({'first_line':a,'last_line':b,'line_count':b-a+1,'normalized_utf8_sha256':sha(span)})
 return out

def tex_census(raw):
 text=raw.decode();labels=[];refs=[];citations=[];bibs=[]
 for line,s in enumerate(text.splitlines(),1):
  for m in re.finditer(r'\\label\{([^}]+)\}',s):labels.append({'label':m[1],'line':line})
  for m in re.finditer(r'\\(?:[cC]ref|eqref|ref|pageref|autoref)\*?\{([^}]+)\}',s):
   refs.extend({'target':k.strip(),'line':line} for k in m[1].split(','))
  for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',s):citations.extend({'key':k.strip(),'line':line} for k in m[1].split(','))
  for m in re.finditer(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',s):bibs.append({'key':m[1],'line':line})
 keys=[x['label'] for x in labels];bibkeys=[x['key'] for x in bibs]
 return {'labels':labels,'label_count':len(labels),'duplicate_labels':sorted({x for x in keys if keys.count(x)>1}),
         'literal_references':refs,'unresolved_literal_references':[x for x in refs if x['target'] not in keys],
         'literal_citations':citations,'bibitems':bibs,'unresolved_literal_citations':[x for x in citations if x['key'] not in bibkeys],
         'scope':'literal regex census only, no TeX expansion/build or external bibliography verification'}

def rank(matrix,n):
 a=[[Fraction(x) for x in row] for row in matrix];r=0
 for j in range(n):
  pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
  if pivot is None:continue
  a[r],a[pivot]=a[pivot],a[r];d=a[r][j];a[r]=[x/d for x in a[r]]
  for i in range(len(a)):
   if i!=r:
    d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[r])]
  r+=1
 return r

def compositions(total,n):
 if n==1:yield (total,);return
 for x in range(total+1):
  for tail in compositions(total-x,n-1):yield (x,)+tail

def phi(n):return sum(math.gcd(k,n)==1 for k in range(1,n+1))
def finite_recheck(doc):
 rays=units=0
 for case in doc['rank_examples']['cases']:
  n=len(case['generators']);a=case['relation_matrix'];J=[i-1 for i in case['positive_generator_indices']];K=[i-1 for i in case['unit_generator_indices']]
  need(sorted(J+K)==list(range(n)) and not set(J)&set(K),'complete unit partition')
  w=case['positive_witness'];need([i for i,v in enumerate(w) if v>0]==J and all(v>=0 for v in w),'positive support')
  need(all(sum(x*y for x,y in zip(row,w))==0 for row in a),'exact positive kernel')
  need(rank(a,n)==case['matrix_rank'] and n-rank(a,n)==case['group_rank'],'group rank')
  ar=[[row[i] for i in J] for row in a]
  need(rank(ar,len(J))==case['restricted_matrix_rank'] and len(J)-rank(ar,len(J))==case['positive_rank'],'positive rank')
  for c in case['positive_circuits']:
   v=c['primitive_vector'];support=[i for i,x in enumerate(v) if x]
   need(all(x>=0 for x in v) and support==[i-1 for i in c['support_indices']] and math.gcd(*v)==1,'primitive circuit')
   need(all(sum(x*y for x,y in zip(row,v))==0 for row in a),'circuit kernel')
   need(rank([[row[i] for i in support] for row in a],len(support))==len(support)-1,'circuit nullity');rays+=1
  covered=[]
  for c in case['unit_certificates']:
   j=c['generator_index']-1;z=c['row_coefficients'];v=c['inverse_exponents'];need(all(x>=0 for x in v),'unit positivity')
   need([sum(z[i]*a[i][k] for i in range(len(a))) for k in range(n)]==[v[k]+int(k==j) for k in range(n)],'integer unit identity');covered.append(j);units+=1
  need(sorted(covered)==sorted(K),'unit certificate coverage')
 necklace_cases=objects=0
 for case in doc['necklaces']['cases']:
  m,n=case['m'],case['n'];comps=list(compositions(m,n));orbits={min(c[i:]+c[:i] for i in range(n)) for c in comps}
  num=sum(phi(e)*math.comb((m+n)//e,m//e) for e in range(1,math.gcd(m,n)+1) if m%e==n%e==0)
  need(num%(m+n)==0 and num//(m+n)==len(orbits)==case['formula']==case['rotation_orbits'],'necklace identity')
  need(len(comps)==case['compositions_examined'],'composition census');objects+=len(comps);necklace_cases+=1
 subcases=candidates=0
 for case in doc['finite_subgroups']['cases']:
  k,D=case['k'],case['D'];elements=list(itertools.product(range(k),range(D)));count=0;examined=0
  for tail in itertools.combinations(elements[1:],D-1):
   S={(0,0),*tail};examined+=1
   if all(((x[0]+y[0])%k,(x[1]+y[1])%D) in S for x in S for y in S):count+=1
  formula=sum(c for c in range(1,math.gcd(D,k)+1) if D%c==k%c==0)
  need(count==formula==case['subgroups_of_order_D']==case['sigma_1_of_gcd'],'subgroup count')
  need(examined==case['candidate_subsets'],'subgroup candidate census');candidates+=examined;subcases+=1
 permcases=pairtests=0
 for case in doc['permutation_pairs']['cases']:
  N,m,n=case['N'],case['m'],case['n'];perms=list(itertools.permutations(range(N)));count=0
  def power(p,e):
   out=tuple(range(N))
   for _ in range(e):out=tuple(p[i] for i in out)
   return out
  for f in perms:
   for g in perms:
    pairtests+=1
    if all(f[g[i]]==g[f[i]] for i in range(N)) and power(f,m)==power(g,n):count+=1
  delta=math.gcd(m,n);coeff=[1]+[0]*N
  for d in range(1,delta+1):
   if delta%d==0:
    for j in range(d,N+1):coeff[j]+=coeff[j-d]
  need(count==math.factorial(N)*coeff[N]==case['commuting_pairs_with_power_relation']==case['factorial_times_coefficient'],'finite labelled actions')
  need(coeff[N]==case['generating_function_coefficient'],'finite generating coefficient');permcases+=1
 return {'rank_cases':len(doc['rank_examples']['cases']),'positive_circuits':rays,'unit_identities':units,'necklace_cases':necklace_cases,'weak_compositions':objects,
         'subgroup_cases':subcases,'candidate_subsets':candidates,'permutation_cases':permcases,'pair_exponent_checks':pairtests,
         'scope':'fresh independently written exact checker of stored finite certificate data; no supplied script execution; no infinite theorem certified by enumeration'}

def build():
 commit=git('rev-parse',COMMIT).decode().strip();parent=git('rev-parse',COMMIT+'^').decode().strip();archives=[];corroboration=None
 for stem,spec in SPECS.items():
  path='docs/incoming/'+stem+'.zip';raw=git('show',commit+':'+path);gitblob=git('rev-parse',commit+':'+path).decode().strip();need(blob(raw)==gitblob,'archive git blob')
  z=zipfile.ZipFile(io.BytesIO(raw));members=[];data={}
  need(len(z.namelist())==len(set(z.namelist())),'duplicate archive names')
  for info in z.infolist():
   if info.is_dir():continue
   b=z.read(info.filename);data[info.filename]=b;root=spec['root']+'/';need(info.filename.startswith(root),'archive root')
   local=info.filename[len(root):];r=spans(b,spec['reads'][local]) if local in spec['reads'] else []
   entry={'path':info.filename,'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b),'crc32':f'{info.CRC:08x}','human_read_spans':r,
          'coverage':'full text read' if r and r[0]['first_line']==1 and r[-1]['last_line']==len(b.decode().splitlines()) and len(r)==1 else 'selected text read' if r else 'hash-only; possibly separately structured-data checked'}
   if local.endswith(('.txt','.tex','.json','.py')):entry['utf8_lines']=len(b.decode('utf-8').splitlines())
   if local==spec['tex']:entry['literal_TeX_census']=tex_census(b)
   members.append(entry)
  checksums=[]
  checksum=spec['root']+'/SHA256SUMS.txt'
  if checksum in data:
   for line in data[checksum].decode().splitlines():
    pin,name=line.split(None,1);name=name.lstrip('*');member=spec['root']+'/'+name
    need(member in data and sha(data[member])==pin,'checksum '+member);checksums.append({'member':member,'sha256':pin})
  diff=git('diff','--no-ext-diff','--no-color',parent,commit,'--',path)
  archives.append({'path':path,'commit':commit,'parent':parent,'blob':gitblob,'bytes':len(raw),'sha256':sha(raw),'diff_bytes':len(diff),'diff_sha256':sha(diff),
                   'members':members,'checksum_manifest_checks':checksums,'supplied_program_execution':False})
  if stem=='commuting_injections_research':corroboration=finite_recheck(json.loads(data['commuting_injections/verification.json']))
 context=[]
 for rev,path,rs,scope in CONTEXT:
  b=git('show',rev+':'+path);context.append({'commit':git('rev-parse',rev).decode().strip(),'path':path,'blob':blob(b),'bytes':len(b),'sha256':sha(b),'human_read_spans':spans(b,rs),'scope':scope})
 return {'schema':'bounded-three-action-archive-review-v1','reviewer_sha256':sha(Path(__file__).read_bytes()),'arrival_commit':commit,'archives':archives,'context':context,
         'commuting_finite_corroboration':corroboration,'totals':{'archives':len(archives),'members':sum(len(a['members']) for a in archives),'checksum_entries_verified':sum(len(a['checksum_manifest_checks']) for a in archives),'human_read_member_lines':sum(r['line_count'] for a in archives for m in a['members'] for r in m['human_read_spans'])},
         'scope':{'all_archives_and_members_hashed':True,'commuting_tex_full_human_read':True,'other_tex_selected_only':True,'supplied_program_execution':False,'builders_or_Lean_executed':False,'PDF_rendered_or_read':False,'external_literature_verified':False,'repository_mutations':False,'new_fixed_arity_Diophantine_compiler':False}}
def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');a=ap.parse_args();r=build();raw=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode()
 if a.output:
  with open(a.output,'xb') as f:f.write(raw)
 else:need(raw==Path(a.expect).read_bytes(),'receipt replay')
 print(json.dumps({'status':'PASS','totals':r['totals'],'finite_corroboration':r['commuting_finite_corroboration']},sort_keys=True))
if __name__=='__main__':main()
