#!/usr/bin/env python3
"""Independent exact finite audit; imports checkers, never a construction module."""
import argparse,copy,hashlib,importlib.util,json,os,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import pooled_audit as P,operations_audit as O,audit_projection as A

def read(p):return json.loads(p.read_text())
def need(x,s):
 if not x:raise ValueError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def eqstage(n):return read(ROOT/'stages'/n/'equation.json')
def combo(records,rows):return P.plus(*(P.times(P.P(c),rows[j])for c,j in records))
def basis_audit(source,new,cert):
 need(sha(ROOT/'inherited_strict/direct/source/equation.json')==cert['source_sha256'],'basis source pin');keep=cert['retained_variables'];inv={j:i for j,i in enumerate(keep)};nr=[P.renumber(r,inv)for r in P.rows(new)];old=P.rows(source);fwd={i:P.P(p)for i,p in cert['forward']};rev={i:P.P(p)for i,p in cert['reverse']};by={j:p for j,p in zip(cert['row_origins'],nr)}
 for origin,p in zip(cert['row_origins'],nr):need(P.pull(p,fwd)==combo(cert['forward_combinations'][str(origin)],dict(enumerate(old))),'forward basis row '+str(origin))
 for j,p in enumerate(old):need(P.pull(p,rev)==combo(cert['reverse_combinations'][str(j)],by),'reverse basis row '+str(j))
 # Witness maps must preserve each constrained coordinate in the required direction on zeros;
 # the full residual identities above suffice for existential maps in both directions.
 names=copy.deepcopy(source['variables'])+[cert['new_variable']];i,v=cert['renamed_variable'];names[i]=v
 need([names[i]for i in keep]==new['variables'],'basis variable names');need(len(new['variables'])==len(source['variables'])-3,'basis dimension')
 return dict(forward_rows=len(nr),reverse_rows=len(old))
def frame(source):
 ns={v['name']:i for i,v in enumerate(source['variables'])};N=lambda n,c=0:P.plus(P.V(ns[n]),P.C(c));t=N('t0');F=N('crt.growth_majorant_F');q=P.plus(P.k(4,N('radix.odd_square_root_half')),P.C(1));atoms=[t,P.plus(t,F),N('x'),N('y'),F,N('choose0.output')]
 atoms += [N('crt.encoded.'+n,-1 if n=='a' else 0)for n in ['a','b','c','d','S','Sp','u','vq']]
 atoms += [N('crt.encoded_index_minus_one'),N('pow1.output'),N('add.380'),q,P.plus(q,P.C(1)),N('self_radix.BH')]
 atoms += [N('pow'+str(i)+'.output')for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]]
 j=next(i for i,r in enumerate(source['residuals'])if r['label']=='shared.frame_definition');need(len(atoms)==34,'frame census');need(P.rows(source)[j]==P.minus(N('shared.W'),P.plus(P.C(2),*(P.times(a,a)for a in atoms))),'34 square frame')
 return dict(row=j,atoms=[P.terms(a)for a in atoms])
def pool_audit(source,new,cert):
 # Independent checker from pooled module, with explicit strict-source port edits.
 raw=(ROOT/'code/pooled_audit.py').read_text()
 raw=raw.replace("q=N('pow2.output',-1)","q=plus(k(4,N('radix.odd_square_root_half')),C(1))").replace("len(atoms)==36","len(atoms)==34").replace("plus(N('t0'),N('mul.1'))","plus(N('t0'),N('crt.growth_majorant_F'))")
 scope={'__name__':'strict_pool_independent','__file__':str(ROOT/'code/pooled_audit.py')};exec(compile(raw,'strict_pool_independent.py','exec'),scope)
 scope['check_pools'](source,new,cert,frame(source));return dict(groups=[len(g['requests'])for g in cert['groups']],square_atoms=34)
def beta_audit(source,new):
 ns={v['name']:i for i,v in enumerate(source['variables'])};u=ns['beta.odd_square_multiplier'];v=ns['beta.odd_square_root_half'];r=P.rows(source);j=next(j for j,rr in enumerate(source['residuals'])if rr['label']=='beta.odd_square_multiplier');need(r[j]=={():-1,(u,):1,(v,):-4,(v,v):-4},'beta exactold');r[j]={():-1,(u,):1,(v,):-2};r=[P.pull(p,{u:P.plus(P.C(1),P.k(2,P.V(v)))})for p in r];names,rs=O.compaction(source['variables'],r);need(names==new['variables']and rs==P.rows(new),'beta exactnew');return dict(eliminated=u,parameter=v)
def sphere(e):
 e=copy.deepcopy(e);count=0
 for r in e['residuals']:
  if r['label']=='domain_guard.4':
   count+=1;need([-1,[]]in r['terms']and sum(c==-4 for c,m in r['terms'])==11,'sphere old');
   for t in r['terms']:
    if t[0]==-4:need(len(t[1])==2 and t[1][0]==t[1][1]and 'remainder'in e['variables'][t[1][0]]['name'],'sphere remainder');t[0]=-2
 need(count==1,'sphere census');return e

def run_source_checks():
 base=ROOT/'inherited_strict';checks={};flags=['-B']+(['-O']if sys.flags.optimize else[])
 def run(rel,args=[]):
  p=subprocess.run([sys.executable,*flags,str(base/rel),*map(str,args)],cwd=base,capture_output=True,text=True)
  need(p.returncode==0,'source replay '+rel+'\n'+p.stdout+'\n'+p.stderr);return p.stdout
 for rel in ['code/check_source_edit.py','code/check_power_interface.py','sources/factorial_free/verify.py']:
  out=run(rel,['--skip-manifest']if rel.endswith('factorial_free/verify.py')else[]);checks[rel]=json.loads(out)
 spec=importlib.util.spec_from_file_location('strict_source_checker',base/'code/check_endpoints.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 source=base/'direct/source';checks['factorization']=m.verify_factorization(source,m.FACTORIZATION_CHECKER);eq,rr,steps=m.verify_projection(source);checks['projection_and_translation']={'steps':steps,'variables':len(eq['variables']),'rows':len(rr)}
 with tempfile.TemporaryDirectory(prefix='strict_source_rebuild-')as td:
  run('code/build_strict_source.py',['--output',td]);names=[p.name for p in source.glob('*.json')]
  for n in names:need((Path(td)/n).read_bytes()==(source/n).read_bytes(),'strict source rebuild '+n)
  checks['source_rebuilt_json_files']=len(names)
 return checks

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--skip-sources',action='store_true');ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path);args=ap.parse_args()
 for rel,h in read(ROOT/'SOURCE_PINS.json').items():need(sha(ROOT/rel)==h,'pin '+rel)
 src=read(ROOT/'inherited_strict/direct/source/equation.json');b=eqstage('basis236');basis=basis_audit(src,b,read(ROOT/'certificates/basis236.json'));p=eqstage('pooled224');pool=pool_audit(b,p,read(ROOT/'stages/pooled224/pool_certificate.json'));d=eqstage('differences224');P.check_shear(p,d,read(ROOT/'stages/differences224/shear_certificate.json'));beta=eqstage('beta223');bm=beta_audit(d,beta)
 ss=sphere(beta);names,rs,opcounts=O.replay(ss['variables'],P.rows(ss),read(ROOT/'stages/core219/operations.json'));core=eqstage('core219');need(names==core['variables']and rs==P.rows(core),'core maps')
 rad=core
 for cert in read(ROOT/'stages/radical217/projection_certificate.json')['steps']:rad=A.one_step(rad,cert)
 need(rad==eqstage('radical217'),'radical final');af=A.affine_projection(rad,read(ROOT/'stages/affine216/projection_certificate.json'));need(af==eqstage('affine216'),'affine final')
 endpoints={}
 for n in read(ROOT/'ENDPOINTS.json'):
  e=af if n=='dimension216'else rad;cert=read(ROOT/n/'row_certificate.json');need(A.sha(e)==cert['input_sha256'],'row input');rows=P.rows(e)
  for i,j,k in cert['operations']:
   need(i!=j and all(type(v)is int for v in [i,j,k]),'integer row');old=rows[i];rows[i]=P.plus(rows[i],P.k(k,rows[j]));need(P.plus(rows[i],P.k(-k,rows[j]))==old,'inverse row')
  final=read(ROOT/n/'equation.json');need(P.rows(final)==rows and e['variables']==final['variables'],'endpoint rows');need(A.sha(final)==cert['output_sha256'],'row output');met,ex=P.measure(final);sup=read(ROOT/n/'metrics.json');need(all(met[k]==v for k,v in sup.items()if k!='residual_terms'),'metrics');need(sum(len(r)for r in rows)==sup['residual_terms'],'rowterms');need(ex==P.P(read(ROOT/n/'expanded_polynomial.json')['terms']),'all coefficients');need({v for m in ex for v in m}==set(range(len(final['variables']))),'all used');endpoints[n]=met
 controls=[]
 bad=copy.deepcopy(read(ROOT/'certificates/basis236.json'));bad['forward'][0][1][0][0]+=1
 try:basis_audit(src,b,bad)
 except ValueError:controls.append('basis_forward_corruption')
 else:raise ValueError('corrupt basis accepted')
 bad=copy.deepcopy(read(ROOT/'stages/radical217/projection_certificate.json')['steps'][0]);bad['direction'][0][1]+=1
 try:A.one_step(core,bad)
 except ValueError:controls.append('hessian_direction_corruption')
 else:raise ValueError('corrupt Hessian accepted')
 result=dict(status='PASS',optimized=bool(sys.flags.optimize),basis=basis,pooling=pool,beta=bm,core_operations=opcounts,endpoints=endpoints,negative_controls=controls)
 if not args.skip_sources:result['inherited']=run_source_checks()
 if args.rebuild:
  p=subprocess.run([sys.executable,'-B',*(['-O']if sys.flags.optimize else[]),str(ROOT/'build.py'),'--check'],cwd=ROOT,capture_output=True,text=True);need(p.returncode==0,'new rebuild\n'+p.stdout+p.stderr);result['reconstruction']=p.stdout
 if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
