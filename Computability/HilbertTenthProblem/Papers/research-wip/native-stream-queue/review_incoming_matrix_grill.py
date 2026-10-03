#!/usr/bin/env python3
"""Read-only archive intake. No archive Python, shell, or verifier executes."""
import argparse, hashlib, json, struct
from array import array
from collections import Counter
from pathlib import Path, PurePosixPath
from zipfile import ZipFile

PINS={
 'Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip':'b494c2b8e516d811cbecf305a748197af2a565882319a86586fec316c5ba8c47',
 'Fixed_Universal_Grill_Polynomial_Package.zip':'467e2b4795fd484b73d94c6a006a84652fea772f1b0f870cac1a1f5d1445bf9b',
 'Fixed_Universal_Grill_Polynomial_Package (1).zip':'e7baac1f3cf2c519d40ffc336424ba28c4d44d81a0ec9ed8f0b1812a8ed00405',
 'Native_Grill_Exact_Degree_Laws_Package.zip':'fd63543ab48425175fc36d145193686b347d2160fd735283cd92a22371354876'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def load(root,name):
 path=root/name;need(sha(path.read_bytes())==PINS[name],'archive pin '+name)
 z=ZipFile(path);names=z.namelist();need(len(names)==len(set(names)),'duplicate ZIP name')
 roots=set();members={}
 for name in names:
  parts=PurePosixPath(name).parts;need(len(parts)>=2 and '..' not in parts and not name.startswith('/'),'safe archive member')
  roots.add(parts[0]);members[str(PurePosixPath(*parts[1:]))]=name
 need(len(roots)==1,'single archive root')
 return z,members
def read(archive,name):return archive[0].read(archive[1][name])
def obj(archive,name):return json.loads(read(archive,name))
def mm(a,b):return [[sum(a[i][k]*b[k][j]for k in range(len(b)))for j in range(len(b[0]))]for i in range(len(a))]
def eye(n):return [[int(i==j)for j in range(n)]for i in range(n)]
def inv(a):
 need(a[0][0]*a[1][1]-a[0][1]*a[1][0]==1,'unimodular block')
 return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]
def block(a,b):return [a[0]+[0,0],a[1]+[0,0],[0,0]+b[0],[0,0]+b[1]]
def Ej(j):return [[1+4*j,2],[-8*j*j,1-4*j]]
def matrix_checks(z):
 s=obj(z,'core/data/semigroup.json');table=obj(z,'core/data/u15_table.json');w=obj(z,'core/evidence/accepting-witness.json')
 need(sha(read(z,'core/data/u15_table.json'))==s['table_sha256'],'matrix table pin')
 # Independent compact transcription already present in the WIP U15 receipt;
 # no package compiler or transcription function is imported.
 columns={'0':'cR2 bR3 cL7 cL6 bR1 bL4 cL8 bL9 cR1 bL11 cR12 cR13 cL2 cL3 cR14',
          '1':'bR1 bR1 cL5 bL5 bL4 bL4 bL7 bL7 bL10 - bR14 bR12 bR12 cR15 bR14'}
 transcribed={}
 for bit,column in columns.items():
  for i,item in enumerate(column.split()):transcribed[chr(65+i)+bit]=None if item=='-'else[int(item[0]=='b'),item[1],chr(64+int(item[2:]))]
 need(table==transcribed,'matches existing independent U15 transcription')
 sigma=list('01ABCDEFGHIJKLMNO[]X');need(s['alphabet']==sigma and s['top_codes']==dict(zip(sigma+['#'],range(1,22))),'literal alphabet codes')
 rules=[]
 for cell in sorted(table):
  tr=table[cell]
  if tr is None:need(cell=='J1','sole halt');continue
  b,d,q=tr;b=str(b)
  if d=='R':rules.extend([(cell+'0',b+q+'0'),(cell+'1',b+q+'1'),(cell+']',b+q+'0]')])
  else:need(d=='L','direction');rules.extend([('0'+cell,q+'0'+b),('1'+cell,q+'1'+b),('['+cell,'['+q+'0'+b)])
 rules += [('J1','X'),('0X','X'),('X0','X'),('1X','X'),('X1','X'),('[X]','X')]
 need([(r['lhs'],r['rhs'])for r in s['rules']]==rules,'all93 rule definitions')
 tiles=[(a,a)for a in sigma]+[(v,u)for u,v in rules]+[('#','#')]
 need([(t['h'],t['g'])for t in s['tiles']]==tiles and len(tiles)==114,'all114 tiles')
 def phi(word):
  p=eye(2)
  for c in word:p=mm(p,Ej(s['top_codes'][c]))
  return p
 t=Ej(0);As=[block(phi(h),Ej(i))for i,(h,g)in enumerate(tiles,1)]
 Bs=[block(inv(phi(g)),mm(mm(inv(t),inv(Ej(i))),t))for i,(h,g)in enumerate(tiles,1)]
 C=block(inv(phi('X#')),t);expected=As+Bs+[C]
 actual=[g['matrix']for g in s['generators']]
 need(actual==expected and len({tuple(sum(a,[]))for a in actual})==229,'all229 literal distinct generators')
 for a in actual:
  inv([r[:2]for r in a[:2]]);inv([r[2:]for r in a[2:]])
  need(all(a[i][j]==0 for i in range(4)for j in range(4)if(i<2)!=(j<2)),'block form')
 vals=[v for a in actual for row in a for v in row]
 need((max(map(abs,vals)),sum(v!=0 for v in vals),sum(abs(v).bit_length()for v in vals))==(63038000,1831,21372),'independent coefficient ledger')
 word=w['input']['configuration_word'];need(word=='[110A0]','accepting interface')
 deriv=[word]
 for rid,pos in w['rewrite_steps']:
  u,v=rules[rid-1];need(word[pos:pos+len(u)]==u,'literal rewrite occurrence');word=word[:pos]+v+word[pos+len(u):];deriv.append(word)
 need(word=='X'and deriv==w['derivation'],'14-step derivation')
 seq=w['inner_tile_sequence'];need(len(seq)==94,'94 tiles')
 h=''.join(tiles[i-1][0]for i in seq);g=''.join(tiles[i-1][1]for i in seq)
 need(deriv[0]+'#'+h==g+'X#','exact correspondence word')
 names=['A'+str(i)for i in seq]+['C']+['B'+str(i)for i in reversed(seq)]
 need(names==w['generator_word']and len(names)==189,'actual normal form')
 byname={g['name']:g['matrix']for g in s['generators']};p=eye(4)
 for n in names:p=mm(p,byname[n])
 target=block(inv(phi(deriv[0]+'#')),t)
 need(p==target==w['product']==w['input']['target'],'entire189-generator product')
 # Direct table execution from nearest-head-first ell=011, r=empty.
 tape={-i-1:int(c)for i,c in enumerate('011')};q='A';head=0;steps=0
 while table[q+str(tape.get(head,0))]is not None:
  b,d,q=table[q+str(tape.get(head,0))];tape[head]=b;head+=1 if d=='R'else-1;steps+=1;need(steps<100,'bounded witness')
 need(q=='J'and tape[head]==1 and steps==7,'independent genuine U15 halt')
 # A genuine valid configuration has one active state/X. Each chosen rewrite
 # consumes it and emits one; contexts require only tape/boundary copies.
 controls=set('ABCDEFGHIJKLMNOX')
 need(all(sum(c in controls for c in u)==sum(c in controls for c in v)==1 for u,v in rules),'all93 rules consume and preserve the sole control/X')
 kept=[t['id']for t in s['tiles']if t['kind']!='copy'or t['letter']in '01[]']
 deleted=[t['id']for t in s['tiles']if t['id']not in kept]
 need(deleted==list(range(3,18))+[20]and len(kept)==98,'exact four-copy tile subset')
 subset=[g for g in s['generators']if g['name']=='C'or g['tile_id']in kept]
 need(len(subset)==197 and set(names)<=set(g['name']for g in subset),'complete retained generator array and accepting word')
 subset_result=dict(inner_tiles=98,generators=197,retained_tile_ids=kept,deleted_copy_tile_ids=deleted,deleted_copy_letters=[s['tiles'][i-1]['letter']for i in deleted],retained_generators=subset,accepting_generator_word=names,target_loader_unchanged=True,scope='Derived fixed-semigroup equivalence for every valid finite U15 input; not all malformed rewrite words, inverse closure, a Diophantine operation bound or an improvement to the existing97-tile GPCP compiler')
 paired=[]
 for r in range(3):
  for mode in ('signed','natural'):
   p=obj(z,f'paired/examples/r{r}-{mode}-sos.json');res=p['residuals'];terms=[t for q in res for t in q['polynomial']]
   for q in res:
    monomials=[tuple(sorted(t['variables']))for t in q['polynomial']]
    need(len(monomials)==len(set(monomials))and all(type(t['coefficient'])is int and t['coefficient']!=0 for t in q['polynomial']),'nonzero combined residual coefficients')
   need(p['r']==r and p['mode']==mode and len(p['natural_auxiliary_variables'])==130*r,'bounded polynomial arity')
   need(len(res)==17*r+(4 if mode=='signed'else 8),'bounded polynomial residual count')
   counts=Counter(len(t['variables'])for t in terms);M=sum((d+1)*n for d,n in counts.items())+len(res);A=len(terms)+len(res)
   expected=(16,12)if r==0 else(11246*r-9036,3804*r-2700)
   if mode=='natural':expected=(40,24)if r==0 else(expected[0]+64,expected[1]+24)
   need((M,A)==expected,'literal exported evaluator gate counts')
   maxdegree=2*max(counts);need(maxdegree==(2 if r==0 and mode=='signed'else 4),'literal exported SOS degree')
   paired.append(dict(r=r,mode=mode,M=M,A=A,witnesses=130*r,residuals=len(res),degree=maxdegree))
 return dict(rules=93,tiles=114,generators=229,distinct=True,all_SL4=True,maximum_entry=63038000,nonzero_entries=1831,magnitude_bits=21372,accepting_tm_steps=7,accepting_rewrite_steps=14,accepting_tiles=94,accepting_generator_product=189,paired_signed_auxiliaries='130r',paired_signed_residuals='17r+4',paired_evaluator_full_operations='28 at r0; 15050r-11736 at r>=1',six_literal_bounded_exports=paired,fixed_arity_unbounded_certificate=False,derived_subset197=subset_result)

def grill_checks(old,new,degree):
 name='reproducibility/frozen/arithmetic/universal.dag';a=read(old,name);b=read(new,name)
 need(a==b and sha(a)=='a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2','same full DAG across revision')
 meta=obj(old,'reproducibility/frozen/arithmetic/universal.json');need(meta==obj(new,'reproducibility/frozen/arithmetic/universal.json'),'same scientific manifest')
 retained=[n for n in old[1]if n.startswith('reproducibility/')]
 need(all(n in new[1]and read(old,n)==read(new,n)for n in retained),'all original reproducibility bytes unchanged')
 consts=meta['constants'];need(len(consts)==8160,'constant count')
 for i,row in enumerate(consts):
  op=row[0]
  if op=='int':need(len(row)==2 and type(row[1])is str,'literal constant');int(row[1])
  elif op in ('pow2','geom4'):need(len(row)==2 and type(row[1])is int and row[1]>=0,'fixed natural power recipe')
  else:need(op in ('add','sub','mul')and len(row)==3 and all(type(v)is int and -i<=v<0 for v in row[1:]),'strict earlier-constant recipes only')
 ib=meta['input_base'];ic=meta['input_count'];counts=Counter();position=0
 for r in meta['inputs']:
  need(r['start']==position and r['domain']=='positive_integer','contiguous positive input definitions');position+=r['count'];counts[r['role']]+=r['count']
 need(position==ic==797141 and counts=={'external':6,'witness':797135},'six external/program ports and witness count')
 need([v['name']for v in meta['inputs'][:6]]==['x','a_e','p_e','s_e','C_e','L_e']and all(v['role']=='external'and v['count']==1 for v in meta['inputs'][:6]),'literal ordinary-input/program interface')
 need(a[:8]==b'CDAGv1\0\0'and(len(a)-8)%17==0,'binary DAG format')
 rows=memoryview(a)[8:];N=len(rows)//17;need(N==3600546,'full paid row count');degs=array('I');ops=Counter()
 need(meta['output']==N-1 and ib>N and meta['row_bytes']==17 and meta['row_struct']=='<Bqq'and meta['magic_hex']==a[:8].hex(),'actual output and disjoint binary namespaces')
 need(meta['source_bytes']==len(a)and meta['source_sha256']==sha(a),'binary source metadata binding')
 def d(v,j):
  if v<0:need(-len(consts)<=v,'valid constant handle');return 0
  if v>=ib:need(v<ib+ic,'valid declared input');return 1
  need(v<j,'acyclic backward gate');return degs[v]
 for j,(op,u,v)in enumerate(struct.iter_unpack('<Bqq',rows)):
  need(op in(0,1,2),'paid binary operation');du,dv=d(u,j),d(v,j);degs.append(du+dv if op==2 else max(du,dv));ops[op]+=1
 need(ops[2]==803517 and ops[0]+ops[1]==2797029 and degs[-1]==71731007,'independent paid ledger and syntactic degree')
 live=bytearray(N);inputs=bytearray(ic);live[-1]=1
 for j in range(N-1,-1,-1):
  if not live[j]:continue
  op,u,v=struct.unpack_from('<Bqq',rows,17*j)
  for x in(u,v):
   if x>=ib:inputs[x-ib]=1
   elif x>=0:live[x]=1
 need(all(live)and all(inputs),'complete gate and supplied-input liveness')
 # Reconstruct every paid finalizer row from the86 declared residual pairs.
 extra=meta['extra'];pairs=extra['residual_pairs'];need(len(pairs)==86,'all86 declared nonunit comparisons')
 one=-consts.index(['int','1'])-1;cursor=N-260;squares=[];total=None
 def emit(op,u,v):
  nonlocal cursor
  need(struct.unpack_from('<Bqq',rows,17*cursor)==(op,u,v),'literal complete finalizer row '+str(cursor));ref=cursor;cursor+=1;return ref
 for u,v in pairs:
  diff=emit(1,u,v);sq=emit(2,diff,diff);squares.append(sq);total=sq if total is None else emit(0,total,sq)
 positive=emit(0,one,total);product=emit(2,extra['native_unit'],positive);output=emit(1,product,one)
 need(cursor==N and output==meta['output']and squares==extra['residual_squares']and positive==extra['finalizer_positive'],'entire paid finalizer/interface binding')
 factors=extra['unit_factors'];need(len(factors)==4 and len(set(factors))==4,'four distinct native factor ports')
 def product_leaves(v):
  if v in factors:return Counter({v:1})
  need(0<=v<N-260,'unit source reference');op,u,w=struct.unpack_from('<Bqq',rows,17*v);need(op==2,'unit is a literal product');return product_leaves(u)+product_leaves(w)
 need(product_leaves(extra['native_unit'])==Counter(factors),'complete four-factor native product')
 raw=read(old,'reproducibility/frozen/arithmetic/grill_program.u32');runs=[v[0]for v in struct.iter_unpack('<I',raw)];g=len(set(runs));m=len(runs);lane=2*m+g+5
 need(sha(raw)=='fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01','literal Grill program pin')
 need((m,g,sum(v>0 for v in runs),max(runs))==(397488,2030,24300,275944),'literal full program census')
 need(lane==797011 and 87*lane+16==69339973 and lane+124==797135,'Report24 exact-law instance/witness arithmetic')
 # Exactness is read/proof-assessed, not independently expanded in this intake.
 return dict(full_DAG_sha256=sha(a),source_bytes=len(a),operations=N,M=ops[2],A=ops[0]+ops[1],syntactic_degree_upper=degs[-1],all_gates_live=True,all_inputs_live=True,full_finalizer_rows=260,complete_nonunit_residuals=86,native_unit_factor_ports=4,external_coordinates=6,language_program_parameters=5,positive_witnesses=797135,revision_same_polynomial=True,unchanged_reproducibility_files=len(retained),fixed_phases=m,distinct_exponents=g,positive_runs=24300,zero_runs=m-24300,native_lane_N=lane,reported_exact_degree_formula_value=87*lane+16,degree_status='Own arithmetic instance of read uniform degree proof; no independent giant degree expansion',ordinary_input_status='Read explicit valid five-parameter slice/loader proof; full semantic/native audit not rerun')

def verify(root):
 archives=[load(root,n)for n in PINS]
 try:
  mr=matrix_checks(archives[0]);gr=grill_checks(archives[1],archives[2],archives[3])
  selected={}
  wanted=['core/PROOF.md','core/loader-audit/U15_DEPENDENCY_AUDIT.md','paired/PROOF.md','fiber/PROOF.md','README.md','article/report23.tex','reproducibility/frozen/arithmetic/FULL_COMPOSITION_PROOF.md','exact-degree/frozen/DEGREE_PROOF.md','reproducibility/research/GENERAL_DEGREE_THEOREM.md']
  for name,z in zip(PINS,archives):selected[name]={n:sha(read(z,n))for n in wanted if n in z[1]}
  return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),archives=PINS,selected_text_pins=selected,matrix=mr,grill=gr,scope='Bounded independent data/source intake only; no archive program executes, no full scientific/API suite or universal proof is reverified; no new operation record')
 finally:
  for z in archives:z[0].close()
def main():
 p=argparse.ArgumentParser();p.add_argument('--incoming',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.incoming)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],matrix_generators=r['matrix']['generators'],derived_subset_generators=r['matrix']['derived_subset197']['generators'],grill=r['grill'])))
if __name__=='__main__':main()
