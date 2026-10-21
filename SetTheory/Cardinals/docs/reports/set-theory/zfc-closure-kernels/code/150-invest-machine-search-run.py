#!/usr/bin/env python3
"""Portable continuation experiments. No external Python packages are needed."""
from pathlib import Path
import argparse, collections, csv, hashlib, itertools, json, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import check_joint_fold as checker

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(test,msg):
 if not test:raise ValueError(msg)
def compile_cpp(src,out,cxx):subprocess.run([cxx,'-O3','-std=c++17',str(src),'-o',str(out)],check=True)
def research_root(path):
 p=Path(path).resolve()
 if (p/'candidate-k218/k218.native.tm').is_file():return p
 p=p/'Computability/BusyBeaver/Research/ZFC'
 need((p/'candidate-k218/k218.native.tm').is_file(),'--repo must name ProveIt or its ZFC research directory')
 return p

def pairs_for(T,start,kind):
 Q=sorted({q for q,b in T})
 if kind=='all':return list(itertools.combinations(Q,2))
 ins=collections.defaultdict(list)
 for action in T.values():ins[action[2]].append(action)
 def marker(q):
  a={v[:2]for v in ins[q]}
  return next(iter(a))[0]if len(a)==1 and next(iter(a))[1]==1 else None
 pure=[q for q in Q if q!=start and marker(q)is not None and all(T[q,b][:2]==(b,1)for b in(0,1))]
 pairs=[(q,r)for q,r in itertools.permutations(pure,2)if marker(q)==marker(r)] if kind=='same' else [(q,r)if marker(q)==0 else(r,q)for q,r in itertools.combinations(pure,2)if marker(q)!=marker(r)]
 return sorted(pairs,key=lambda qr:(any(T[qr[0],b]==T[qr[1],b]for b in(0,1)),qr))

def finite_domain(Z,out,T,start,mode,cxx):
 """Finite discovery cases, explicitly not an inductive binary invariant."""
 source=Z/'candidate-k218/sites218.json';rows=json.loads(source.read_text())
 case=out/'finite';case.mkdir();(case/'sites.json').write_bytes(source.read_bytes())
 (case/'sites01.txt').write_text(''.join(f'{p} {op} {0 if k is None else k}\n'for p,op,k in rows))
 can=json.loads((Z/'candidate-k218/canonicalization.json').read_text());boot=can['startup']
 if mode=='masked':
  subprocess.run([sys.executable,str(ROOT/'code/generate_invariants221.py'),str(case)],stdout=open(case/'generation.log','w'),check=True)
  (case/'candidate.tm').write_bytes((Z/'candidate-k218/k218.native.tm').read_bytes())
  dump(case/'proof.json',{'source_sha256':sha(source),'table_sha256':can['table_sha256'],'physical_map':boot['physical_map'],'startup':{'steps':boot['steps'],'head':boot['head'],'header':boot['header'],'logical_seed':boot['logical_registers'],'complete_one_cells':boot['one_cells']}})
  subprocess.run([sys.executable,str(ROOT/'code/check_invariants221.py'),str(case)],stdout=open(case/'independent.log','w'),check=True)
  compile_cpp(ROOT/'code/masked_contexts.cpp',case/'contexts',cxx)
  cmd=[str(case/'contexts'),str(Z/'candidate-k218/k218.native.tm'),str(case/'sites01.txt'),str(case/'masks.txt'),str(case/'contexts.txt')]
 else:
  compile_cpp(ROOT/'code/onespare_contexts.cpp',case/'contexts',cxx)
  cmd=[str(case/'contexts'),str(Z/'candidate-k218/k218.native.tm'),str(case/'sites01.txt'),str(case/'contexts.txt')]
 with open(case/'context-generation.log','w')as log:subprocess.run(cmd,stdout=log,stderr=log,check=True)
 I={q:set()for q,b in T}
 for line in (case/'contexts.txt').read_text().splitlines():
  v=list(map(int,line.split()));I[v[0]].update(v[1:])
 q=start;h=0;ones=set();radius=9
 for tick in range(boot['steps']):
  I[q].add(sum(int(h+k in ones)<<(k+radius)for k in range(-radius,radius+1)))
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 need((q,h,sorted(ones))==(84,boot['head'],boot['one_cells']),'literal startup mismatch')
 dump(case/'domain.json',{q:sorted(v)for q,v in I.items()})
 return I

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,help='ProveIt checkout or the ZFC research directory')
 ap.add_argument('--output',type=Path,required=True,help='Fresh output directory')
 ap.add_argument('--mode',choices=['allinitial','onespare','masked','complemented','control','marker-control','incoming-variant'],default='allinitial')
 ap.add_argument('--pairs',choices=['opposite','same','all'],default='opposite')
 ap.add_argument('--seconds',type=int,default=180)
 ap.add_argument('--cxx',default='g++');a=ap.parse_args()
 need(not a.output.exists(),'output must be a fresh directory');out=a.output.resolve();out.mkdir(parents=True)
 if a.mode=='incoming-variant':
  old=ROOT/'data/incoming-k218.native.tm';new=ROOT/'data/incoming-row157.native.tm'
  subprocess.run([sys.executable,str(ROOT/'code/check_joint_fold.py'),'--old',str(old),'--new',str(new),'--radius','7','--fuel','97','--output',str(out/'proof.json')],check=True)
  return
 cpp=ROOT/'code'/('flipped_fast.cpp'if a.mode in('complemented','marker-control')else'twoaction_fast.cpp')
 compile_cpp(cpp,out/'twoaction_fast',a.cxx)
 if a.mode in('control','marker-control'):
  stem='flipped_control'if a.mode=='marker-control'else'twoaction_control'
  inp=ROOT/('data/'+stem+'.input');old=ROOT/('data/'+stem+'.native.tm');pairs=[(1,2)];T,start=checker.read(old);radius=3;fuel=97
 else:
  need(a.repo is not None,'--repo is required for a research search');Z=research_root(a.repo);old=Z/'candidate-k218/k218.native.tm';T,start=checker.read(old)
  need(sha(old)=='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f','unexpected baseline table')
  radius,fuel=(7,97)if a.mode in('allinitial','complemented')else(9,197)
  I=checker.domain(T,start,radius)if a.mode in('allinitial','complemented')else finite_domain(Z,out,T,start,a.mode,a.cxx)
  Q=sorted({q for q,b in T})
  if a.mode=='complemented':
   if a.pairs=='all':
    directions=collections.defaultdict(set)
    for w,d,z in T.values():directions[z].add(d)
    pairs=[(q,r)for q,r in itertools.permutations(Q,2)if r!=start and len(directions[r])==1]
   else:
    need(a.pairs=='same','complemented mode requires --pairs same or --pairs all');pairs=pairs_for(T,start,'same')
  else:pairs=pairs_for(T,start,a.pairs)
  inp=out/'input.txt'
  with inp.open('w')as f:
   print(radius,fuel,start,len(Q),file=f)
   for q in Q:print(q,*T[q,0],*T[q,1],len(I[q]),*sorted(I[q]),file=f)
   print(len(pairs),file=f)
   for pair in pairs:print(*pair,file=f)
 began=time.monotonic();prefix=out/'search'
 with open(out/'search.log','w')as log:subprocess.run([str(out/'twoaction_fast'),str(inp),str(prefix),str(a.seconds)],stdout=log,stderr=log,check=True)
 records=[{k:int(v)for k,v in row.items()}for row in csv.DictReader(open(str(prefix)+'-records.tsv'),delimiter='\t')]
 hits=[]
 for p in sorted(out.glob('search-hit*.native.tm')):
  row=next(r for r in records if r['survivors']);N,ns=checker.read(p);h={'file':p.name,'keep':row['keep'],'drop':row['drop'],'sha256':sha(p)}
  if a.mode in ('control','allinitial'):
   proof=checker.check(T,N,start,ns,row['keep'],row['drop'],radius,fuel)
   bad=N.copy();bad[ns,0]=(0,1,254)
   try:checker.check(T,bad,start,ns,row['keep'],row['drop'],radius,fuel)
   except ValueError as exc:proof['negative_control']={'status':'REJECTED','reason':str(exc)}
   else:raise ValueError('initial halt negative control passed')
   dump(out/(p.stem+'-proof.json'),proof);h['independent_status']=proof['status']
  elif a.mode in ('complemented','marker-control'):
   import check_marker_fold
   dirs={d for w,d,z in T.values()if z==row['drop']};need(len(dirs)==1,'marker entry direction');tag=-next(iter(dirs))
   proof=check_marker_fold.verify(T,N,start,ns,row['keep'],row['drop'],tag,radius,fuel)
   bad=N.copy();bad[ns,0]=(0,1,254)
   try:check_marker_fold.verify(T,bad,start,ns,row['keep'],row['drop'],tag,radius,fuel)
   except ValueError as exc:proof['negative_control']={'status':'REJECTED','reason':str(exc)}
   else:raise ValueError('initial halt marker control passed')
   dump(out/(p.stem+'-proof.json'),proof);h['independent_status']=proof['status']
  else:h['independent_status']='FINITE_DISCOVERY_ONLY_REQUIRES_UNBOUNDED_PROOF'
  hits.append(h)
 complete=len(records)==len(pairs)and all(r['complete']for r in records)
 result={'status':'COMPLETE_BOUNDED_SEARCH'if complete else'HIT_OR_INCOMPLETE_LIMIT','mode':a.mode,'pairs_family':'single prescribed synthetic pair'if a.mode in('control','marker-control')else a.pairs,'radius':radius,'fuel':fuel,'working_states':len(T)//2,'pair_count':len(pairs),'pairs_finished':sum(r['complete']for r in records),'pair_records':len(records),'partial_checks':sum(r['partial_checks']for r in records),'complete_assignments_rejected':sum(r['covered_rejections']for r in records),'expected_complete_assignments':len(pairs)*(4*(len(T)//2))**2,'hits':hits,'seconds':time.monotonic()-began,'baseline_sha256':sha(old),'input_sha256':sha(inp),'cpp_sha256':sha(cpp),'configuration_relation':'complemented-entry-marker'if a.mode in('complemented','marker-control')else'identity-tape','records_sha256':sha(str(prefix)+'-records.tsv'),'scope':'Both merged rows independently range over every write bit, direction and surviving-state/halt target. Other rows are mapped unchanged for same-tape searches; complemented-marker searches also complement writes on entry to the removed state. Demand-driven failure before reading an unassigned row prunes every completion of that row. Covered assignments are not all explicitly simulated. Rejections of finite local diagrams are not semantic counterexamples or a lower bound. Finite source-mask and spare-tail domains are discovery filters only.'}
 dump(out/'result.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
