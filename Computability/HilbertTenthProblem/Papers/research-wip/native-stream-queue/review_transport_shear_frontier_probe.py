#!/usr/bin/env python3
"""Independent bounded saved-source audit; not a new partition census."""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
from types import ModuleType

PINS={
 'transport_shear_frontier_probe.py':'ffb0e51d33a7cca4867c47c91a2f4b49b78f4765608ec59e875abfc6bf3acde4',
 'transport_shear_frontier_probe.json':'4e58078d955a9cc7d5642dea24e8f1ac76ac71da2f8b82b568bb27794d25d865',
 'transport_shear_frontier_probe.md':'76b91c800ebfe3ea8dd66bcf274d46ff773eebc8d7a73811d929c465f42bd82e',
 'complete75_asymmetric_factor_partitions.json':'6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f',
 'complete75_asymmetric_factor_partitions.md':'1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2',
 'complete75_asymmetric_factor_partitions.py':'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515',
 'complete75_asymmetric_linear_gap_tradeoffs.json':'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26',
 'complete75_asymmetric_linear_gap_tradeoffs.md':'93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638',
 'complete75_asymmetric_linear_gap_tradeoffs.py':'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2',
 'complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98',
 'complete75_asymmetric_scale_tradeoffs.md':'3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2',
 'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660',
 'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
 'complete86_first_root_partitions.md':'7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0',
 'complete86_first_root_partitions.py':'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988',
 'complete86_transport_quotient_shear.json':'77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc',
 'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
 'complete86_transport_quotient_shear.py':'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45',
 'review_complete86_transport_quotient_shear.py':'122476fcc03f8fb83a0971385fc9782f6b077b0f3012da01b9bfa2fe3b5e5262',
 '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}
CONST=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
SELECTED={('first_root_saved',2):(88,122),('older_linear_gap_saved',0):(89,112),('older_linear_gap_saved',1):(90,108),('older_linear_gap_direct',0):(89,112),('older_linear_gap_direct',7):(90,108)}
def need(test,msg):
 if not test:raise AssertionError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))

def plus(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items()if v}
def times(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   key=tuple(x+y for x,y in zip(m,n));c[key]=c.get(key,0)+v*w
 return {m:v for m,v in c.items()if v}

def finalizer(rows,out):
 # Independent complete formal expansion in actual norm/comparison ports.
 defs={n:(op,a,b)for n,op,a,b in rows};factors=[n for n in FACTORS if n in defs];atoms=factors+['strong_residual','linear_residual'];k=len(atoms);zero=(0,)*k
 unit=lambda i:{tuple(int(i==j)for j in range(k)):1}
 constant=lambda v:{zero:v}if v else{}
 e={}
 for n,op,a,b in rows:
  if n in factors:e[n]=unit(factors.index(n));continue
  if (op,a,b)==('-','ic22','R16'):e[n]=unit(len(factors));continue
  if op=='-'and set((a,b))=={'H17','aux_u_rhs'}:e[n]=unit(len(factors)+1);continue
  if not all(type(v)is int or v in e for v in(a,b)):continue
  aa=constant(a)if type(a)is int else e[a];bb=constant(b)if type(b)is int else e[b]
  e[n]=times(aa,bb)if op=='*'else plus(aa,bb,1 if op=='+'else-1)
 need(out in e,'complete finalizer reached from all actual factors/comparisons')
 full=tuple([1]*len(factors)+[0,0]);prod=plus({full:1},constant(1),-1)
 if e[out]==prod:return factors,[list(range(len(factors)))],[],'product_minus_one',e[out]
 groups=[]
 for mon,coef in e[out].items():
  if coef==-2 and not any(mon[len(factors):]) and set(mon)<=set((0,1)):
   group=[i for i,x in enumerate(mon[:len(factors)])if x];need(group,'nonempty group');groups.append(group)
 groups.sort();need(sorted(i for g in groups for i in g)==list(range(len(factors))),'each factor occurs in exactly one group')
 rebuilt={}
 for g in groups:
  mon=tuple(int(i in g)for i in range(k));r=plus({mon:1},constant(1),-1);rebuilt=plus(rebuilt,times(r,r))
 comparisons=[]
 for j,degree in ((len(factors),22),(len(factors)+1,6)):
  square=times(unit(j),unit(j));mon=next(iter(square))
  if e[out].get(mon):need(e[out][mon]==1,'unit coefficient on retained comparison square');rebuilt=plus(rebuilt,square);comparisons.append(degree)
 need(rebuilt==e[out],'entire finalizer is genuine SOS of groups and retained comparisons')
 return factors,groups,comparisons,'sum_of_squares',e[out]

def inspect_source(old,new,out):
 need(len(old)==len(new),'no hidden deleted/added gates')
 expected=copy.deepcopy(old);d={n:(op,a,b)for n,op,a,b in old}
 required={'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),'wn2':('*','w','q'),'q_minus_F':('-','q','F'),'q_minus_FZ':('-','q_minus_F','Z'),'C_after_alpha':('-','q_minus_FZ','alpha'),'scaled_t':('*','twice_cell_bits','x'),'marked_rhs':('-','C_after_alpha','scaled_t'),'kinner':('+','Kconstant','wn2'),'innerC':('*','kinner','marked_rhs'),'transport_partial':('+','innerC','q_minus_F'),'local_rhs':('*','zplus','repunit'),'norm_transport':('-','transport_partial','local_rhs')}
 need(all(d.get(n)==r for n,r in required.items()),'actual shear/content definitions')
 need([n for n,op,a,b in old if 'zplus'in(a,b)]==['local_rhs'],'private quotient')
 need([n for n,op,a,b in old if 'kinner'in(a,b)]==['innerC'],'private coefficient')
 for row in expected:
  if row[0]=='kinner':row[3]='w'
  if row[0]=='local_rhs':row[2]='transport_quotient'
 need(expected==new,'complete literal reconstruction')
 defined={n for n,op,a,b in new};free=sorted({v for n,op,a,b in new for v in(a,b)if type(v)is str}-defined)
 witnesses=sorted(set(free)-set(CONST+['x']));need(len(witnesses)==19 and set(CONST+['x'])<=set(free),'nineteen positive witness ports')
 degrees={n:0 if n in CONST else 1 for n in free};deps={};counts=Counter()
 for n,op,a,b in new:
  need(n not in degrees and op in('+','-','*')and all(type(v)is int or v in degrees for v in(a,b)),'source closure')
  ds=[0 if type(v)is int else degrees[v]for v in(a,b)];degrees[n]=sum(ds)if op=='*'else max(ds);deps[n]=(a,b);counts['M'if op=='*'else'A']+=1
 seen=set();todo=[out]
 while todo:
  n=todo.pop()
  if type(n)is int or n in seen:continue
  seen.add(n);todo.extend(deps.get(n,()))
 need(seen==set(deps)|set(free),'complete source/free-port liveness')
 ids={}
 def intern(key):
  if key not in ids:ids[key]=len(ids)
  return ids[key]
 def expressions(rows):
  e={n:intern(('free',n))for n in free+['zplus']}
  for n,op,a,b in rows:
   aa=intern(('int',a))if type(a)is int else e[a];bb=intern(('int',b))if type(b)is int else e[b]
   e[n]=intern(('proved_transport_identity',))if n=='norm_transport'else intern((op,aa,bb))
  return e
 a=expressions(old);b=expressions(new);retained=[n for n,op,x,y in old if n not in('kinner','innerC','transport_partial','local_rhs')]
 need(all(a[n]==b[n]for n in retained),'all retained registers and entire output at proved cut');need(a[out]==b[out],'full finalizer pullback')
 return dict(operations=len(new),M=counts['M'],A=counts['A'],syntactic_degree=degrees[out]),free,witnesses,len(retained)

def inherited_weights(rows,factors):
 d={n:(op,a,b)for n,op,a,b in rows}
 # Exact factor degrees/leading forms read in the authenticated predecessor
 # proofs; literal producer choices identify which proved base is present.
 firstroot=d['tau_square']==('*','tau_root','tau_root');normalized=d.get('strong_difference')==('*','A','ic22')
 linear=d['index_product']==('*','delta','a_plus_one');gap=d.get('y_aux')==('+','aux_u_rhs','aux_gap');coupled=d.get('norm_linear')==('+','linear_difference','index_difference')
 weights=dict(zip(FACTORS,[22 if firstroot else 12,18,20 if linear else 32,56 if normalized else 20 if gap else 24,7,2,34 if normalized else 22,7 if coupled else 6]))
 return [weights[n]for n in factors]

def verify(root,artifact_root):
 blobs={}
 for name,pin in PINS.items():
  path=(artifact_root/name)if name.startswith('transport_shear_frontier_probe.')else(root/name)
  blobs[name]=path.read_bytes();need(sha(blobs[name])==pin,'source pin '+name)
 receipt=json.loads(blobs['transport_shear_frontier_probe.json']);need(receipt['source_sha256']==PINS['transport_shear_frontier_probe.py'],'author receipt source hash')
 # Reuse ONLY our earlier independent ring/dense/scalar engines, compiled
 # from pinned bytes. Its verify and every author module remain unexecuted.
 engine=ModuleType('previous_independent_shear_arithmetic');engine.__file__=str(root/'review_complete86_transport_quotient_shear.py');exec(compile(blobs['review_complete86_transport_quotient_shear.py'],engine.__file__,'exec'),engine.__dict__)
 localhash=engine.local_ring_identity()
 a=json.loads(blobs['complete86_first_root_partitions.json']);b=json.loads(blobs['complete75_asymmetric_factor_partitions.json']);c=json.loads(blobs['complete75_asymmetric_linear_gap_tradeoffs.json'])
 families=[('first_root_saved',a['frontier_sources']),('older_asymmetric_saved',b['emitted']),('older_linear_gap_saved',c['emitted']),('older_linear_gap_direct',c['direct_transfers'])]
 need([len(v)for n,v in families]==[13,5,10,11]and len(a['winner_ledgers'])==101,'bounded source inventory only')
 originals={(family,i):item for family,items in families for i,item in enumerate(items)}
 need(len(receipt['forms'])==len(originals)==39,'all thirty-nine saved forms')
 counts=Counter();summaries=[];selected=[];observed=set();points=set()
 for f in receipt['forms']:
  key=(f['family'],f['index']);need(key in originals and key not in observed,'unique saved source mapping');observed.add(key);p=originals[key];old=p.get('source',p.get('polynomial_source'));new=f['source'];out=p['output']
  need(out==f['output']and sha(json.dumps(old,separators=(',',':')).encode())==f['parent_complete_source_sha256'],'exact parent source attribution')
  ledger,free,witnesses,nret=inspect_source(old,new,out);need(witnesses==f['witnesses']and f['ordinary_input']=='x'and f['fixed_numerals']==CONST,'saved interface')
  need(all(ledger[n]==f[n]for n in('operations','M','A'))and ledger['syntactic_degree']==f['raw_syntactic_upper_degree'],'whole source ledger')
  factors,groups,comparisons,kind,formal=finalizer(new,out);weights=inherited_weights(new,factors)
  groupweights=[sum(weights[i]for i in group)for group in groups];degree=sum(weights)if kind=='product_minus_one'else 2*max(groupweights+comparisons)
  cert=f['degree_proof'];need(cert['factors']==factors and cert['factor_degrees']==weights and sorted(cert['groups'])==groups and sorted(cert['group_degrees'])==sorted(groupweights)and cert['retained_residual_degrees']==comparisons and cert['finalizer']==kind and f['degree']==cert['exact_degree']==degree,'formal exact degree certificate')
  ow=weights[:];ow[factors.index('norm_transport')]=3;og=[sum(ow[i]for i in g)for g in groups];olddegree=sum(ow)if kind=='product_minus_one'else 2*max(og+comparisons)
  recorded=p.get('exact_degree',p.get('degree_certificate',{}).get('exact_degree'))
  if recorded is None:
   matches=[d['degree']for d in c['degree_audit']if d['mode']=='direct'and d['name']==p['name']];need(matches and len(set(matches))==1,'actual direct parent degree');recorded=matches[0]
  need(recorded==f['parent_degree']==olddegree,'inherited actual parent degree')
  counts['saved_full_source_identities']+=1;counts['retained_register_identities']+=nret;counts['live_paid_gates']+=len(new);counts['actual_unit_forcing_finalizers']+=1;counts[kind]+=1;points.add((len(new),degree))
  summaries.append({'family':key[0],'index':key[1],'ledger':ledger,'degree':degree,'parent_degree':olddegree,'finalizer':kind,'factor_degrees':weights,'groups':groups,'retained_comparison_degrees':comparisons})
  if key not in SELECTED:continue
  need((len(new),degree)==SELECTED[key]and kind=='product_minus_one'and len(factors)==8,'three extra winning points and direct aliases')
  dense_receipts=[]
  for case,B in enumerate((16,32,64)):
   ev={n:[(i+case)%5-2,(2*i+case)%7+1]for i,n in enumerate(witnesses+['x'])}
   # Do not choose delta=2*rho or 2*g=k, which would erase a leading
   # form in this finite specialization. The uniform proof is separate.
   ev['delta'][1]=1;ev['rho'][1]=3;ev['eta'][1]=2;ev['zeta'][1]=3
   if 'tau_gap'in ev:ev['tau_gap'][1]=1
   fixed=dict(Bm1=B-1,Kconstant=5+3*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=5,MC=B+2,MF=2*B+3);ev.update({n:[x]for n,x in fixed.items()})
   child=engine.polynomial_run(new,ev);back=copy.deepcopy(ev);back['zplus']=engine.add(back.pop('transport_quotient'),engine.mul(ev['w'],child['marked_rhs']));parent=engine.polynomial_run(old,back)
   need(all(child[n]==parent[n]for n in factors+[out]),'every exact integer coefficient of selected entire pullback')
   need([len(child[n])-1 for n in factors]==weights and len(child[out])-1==degree,'selected exact factor/full degrees')
   top={n:v[1]for n,v in ev.items()if n not in CONST};Q=fixed['Bm1']*top['Jrep'];kk=top['eta']+top['zeta'];gg=top['rho']+top['sigma'];Ct=Q-top['F']-top['Z']-top['alpha']-fixed['twice_cell_bits']*top['x']
   leaders=[-top['w']**2*top['s']**4*kk**2*Q**14 if 'tau_root'in witnesses else top['w']*top['s']**2*kk*Q**7*(2*top['tau_gap']-kk),8*gg*kk*top['w']**2*top['s']**3*Q**11,4*top['delta']*(2*top['rho']-top['delta'])*top['w']**3*top['s']**3*Q**12,2*top['aux_gap']*top['f']**2*kk*top['w']**2*top['s']**3*Q**11 if 'aux_gap'in witnesses else top['f']**2*kk**2*top['w']**2*top['s']**4*Q**14,-top['h']*top['w']*top['s']*Q**4,top['w']*Ct-top['transport_quotient']*Q,top['i']**2*kk**4*top['s']**4*Q**12,-top['h']*top['w']*top['s']*Q**4]
   need([child[n][-1]for n in factors]==leaders and all(leaders),'actual leading forms for all eight winning-source factors')
   product=1
   for v in leaders:product*=v
   need(child[out][-1]==product,'complete selected nonzero leader')
   dense_receipts.append({'B':B,'exact_degree':degree,'full_coefficients_sha256':sha(stable(child[out]).encode())});counts['selected_exact_dense_pullbacks']+=1;counts['selected_factor_leader_checks']+=8
  rng=random.Random(935+len(new)+key[1])
  for i in range(16):
   values={n:rng.randrange(-3,5)for n in free}
   if i>=12:values={n:Fraction(v,5)for n,v in values.items()};counts['selected_rational_cases']+=1
   inverse=dict(values);content=values['Bm1']*values['Jrep']+1-values['F']-values['Z']-values['alpha']-values['twice_cell_bits']*values['x'];inverse['zplus']=inverse.pop('transport_quotient')+values['w']*content
   x=engine.scalar_run(old,inverse);y=engine.scalar_run(new,values);need(all(x[n]==y[n]for n in factors+[out]),'complete selected signed/rational pullback');counts['selected_numeric_pullbacks']+=1
  if 'aux_gap'in witnesses:
   values={n:1 for n in free};values.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
   child=engine.scalar_run(new,values);need(child['y_aux']<0,'computed auxiliary ordinate is not a supplied positivity premise');counts['negative_computed_auxiliary_cases']+=1
  selected.append({'family':key[0],'index':key[1],'operations':len(new),'M':ledger['M'],'A':ledger['A'],'exact_degree':degree,'dense_checks':dense_receipts})
 need(set(originals)==observed and len(selected)==5,'complete requested saved-source and alias coverage')
 frontier=sorted(p for p in points if not any(q!=p and q[0]<=p[0]and q[1]<=p[1]for q in points));need([list(p)for p in frontier]==receipt['saved_schedule_frontier'],'bounded saved-source nondominance only')
 return {'status':'PASS independent bounded saved-source transfer review','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'counts':dict(counts),'local_identity_sha256':localhash,'selected_winning_sources':selected,'all_saved_source_summaries':summaries,'saved_schedule_frontier':[list(p)for p in frontier],'scope':'All39 literal saved source/ledger/full-finalizer/unit-forcing and inherited degree certificates checked; exact dense full coefficient/leader checks focus on three additional winners and two direct aliases. No author Python, old verify,101-plan reconstruction or partition search executed; prior independent arithmetic engine reused by pinned bytes. No full native Pell zero or maintained compiler/API claim.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifact-root',type=Path,default=Path('/tmp'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifact_root);encoded=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.expect:need(a.expect.read_text()==encoded,'fresh exact review receipt')
 if a.output:a.output.write_text(encoded)
 print(r['status'],r['counts']);print(r['saved_schedule_frontier'])
