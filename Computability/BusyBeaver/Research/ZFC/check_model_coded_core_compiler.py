"""Fresh-check four template modules and two audits, optionally adding the PA client.

No Lake/dependency build/fetch occurs. Cached dependency objects are identified,
not rebuilt or independently attested as a whole. Source matrices may have
nonstandard codes; the source proof trees remain standard finite syntax.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULES=('TypedTemplateProofCompiler','ModelCodedPredicateTemplate','ModelCodedPredicateHygiene','ModelCodedCoreCompiler')
PROVIDERS=('Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding','Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1')
PINS={'lib/FormalizedFormalLogic-Foundation':'32e1a0956a8622fad067328ca1959729a7634428','.lake/packages/mathlib':'81a5d257c8e410db227a6665ed08f64fea08e997'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sources',type=Path,required=True);p.add_argument('--dependency-root',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--hygiene-audit',type=Path,required=True);p.add_argument('--core-audit',type=Path,required=True);p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--peano-audit',type=Path);a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use Python -O.')
 src=a.sources.resolve();root=a.dependency_root.resolve();work=a.output.resolve();lean=a.lean.resolve()
 assert not work.exists() or not any(work.iterdir()),'Use fresh scratch output.'
 assert not work.is_relative_to(src) and not work.is_relative_to(root)
 work.mkdir(parents=True,exist_ok=True);cache=work/'cache';cache.mkdir();snapshot=work/'sources';(snapshot/'BoundedPAConsistency').mkdir(parents=True)
 version=subprocess.check_output([str(lean),'--version'],text=True).strip();assert 'version 4.32.0,' in version
 libs=[x.resolve() for x in a.library_path] or [root/'.lake/packages/mathlib/.lake/build/lib/lean']+sorted(q for q in (root/'.lake/packages').glob('*/.lake/build/lib/lean') if q!=root/'.lake/packages/mathlib/.lake/build/lib/lean')+[root/'.lake/build/lib/lean']
 assert all(q.is_dir() for q in libs)
 d={'status':'RUNNING','scope':__doc__,'scratch':str(work),'compiler':{'path':str(lean),'version':version},'dependencies':{},'providers':[],'modules':{},'audits':[],'commands':[],'dependency_build':False,'fetch':False,'LEAN_PATH':':'.join(map(str,[cache]+libs))}
 for rel,pin in PINS.items():
  q=root/rel;commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=q,text=True).strip();clean=not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=q,text=True).strip();assert commit==pin and clean;d['dependencies'][rel]={'path':str(q),'pin':commit,'tracked_clean':clean}
 for mod in PROVIDERS:
  rel=Path(mod.replace('.','/'));q=root/'lib/FormalizedFormalLogic-Foundation'/rel.with_suffix('.lean');obj=next((x/rel.with_suffix('.olean') for x in libs if (x/rel.with_suffix('.olean')).is_file()),None);assert q.is_file() and obj is not None;d['providers'].append({'module':mod,'source':str(q),'source_sha256':sha(q),'object':str(obj),'object_sha256':sha(obj)})
 inputs=[lean]+[q[k] for q in d['providers'] for k in ('source','object')]
 for mod in MODULES + (('ModelCodedPeanoCore',) if a.peano_audit else ()):
  original=src/'BoundedPAConsistency'/(mod+'.lean');q=snapshot/'BoundedPAConsistency'/(mod+'.lean');shutil.copyfile(original,q);d['modules'][mod]={'original':str(original),'source':str(q),'source_sha256':sha(q)};inputs += [original,q]
 audits=[(a.hygiene_audit,'ModelCodedPredicateHygieneAudit',2,6),(a.core_audit,'ModelCodedCoreCompilerAudit',4,8)]
 if a.peano_audit:audits.append((a.peano_audit,'ModelCodedPeanoCoreAudit',3,6))
 for original,label,probes,callers in audits:
  q=snapshot/(label+'.lean');shutil.copyfile(original,q);body=q.read_text();assert len(re.findall(r'^#print axioms ',body,re.M))==probes and len(re.findall(r'^example\b',body,re.M))==callers;d['audits'].append({'source':str(q),'source_sha256':sha(q),'probes':probes,'callers':callers});inputs += [original,q]
 d['before']={str(q):sha(q) for q in inputs}
 env=dict(os.environ,LEAN_PATH=d['LEAN_PATH'],LEAN_NUM_THREADS='1')
 def save():(work/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 def run(label,q,obj=None):
  cmd=[str(lean)]+(['-o',str(obj)] if obj else [])+[str(q)];t=time.monotonic();r=subprocess.run(cmd,cwd=snapshot,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out);d['commands'].append({'label':label,'command':cmd,'cwd':str(snapshot),'exit_code':r.returncode,'seconds':time.monotonic()-t,'output':out});save();assert r.returncode==0 and 'sorryAx' not in out and "declaration uses 'sorry'" not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 for mod,info in d['modules'].items():
  obj=cache/'BoundedPAConsistency'/(mod+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);run(mod,Path(info['source']),obj);info.update(object=str(obj),object_sha256=sha(obj))
 for info in d['audits']:
  q=Path(info['source']);out=run(q.stem,q);axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out,re.S);assert len(axioms)==info['probes'];assert all(set(x.strip() for x in row.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for row in axioms);info['only_standard_axioms']=True
 d['after']={str(q):sha(q) for q in inputs};assert d['before']==d['after'];d.update(status='PASS',all_inputs_providers_compiler_unchanged=True,checker=str(Path(__file__).resolve()),checker_sha256=sha(__file__));save();print(work/'verification.json')
if __name__=='__main__':main()
