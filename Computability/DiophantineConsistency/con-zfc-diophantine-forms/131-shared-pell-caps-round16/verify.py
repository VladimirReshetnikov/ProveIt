#!/usr/bin/env python3
"""Offline finite replay in an isolated copy. Python standard library only.
Checks remain active under -O. This does not prove consistency, universal
Pell theorems, or a new machine-checked logical calibration.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def require(ok,message):
 if not ok:raise ValueError(message)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);ap.add_argument('--mode',choices=['both','normal','optimized'],default='both');a=ap.parse_args()
 begin=time.monotonic();r={'status':'RUNNING','scope':'Exact finite algebra, authentic coefficients, byte-exact reconstruction and corruption controls; ordinary unbounded semantics and calibration remain separate.','mode':a.mode,'commands':[],'byte_equalities':[]}
 mf=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())['files']
 for name,row in mf.items():
  p=ROOT/name;require(p.is_file(),'Missing manifest file '+name);require(p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'Manifest mismatch '+name)
 r['manifest_files']=len(mf)
 for row in json.loads((ROOT/'architecture/SOURCE_CLOSURE.json').read_text())['files']:
  p=ROOT/'architecture'/row['path'];require(digest(p)==row['sha256'] and p.stat().st_size==row['bytes'],'Architecture source closure '+row['path'])
 modes=[False,True] if a.mode=='both' else [a.mode=='optimized']
 with tempfile.TemporaryDirectory(prefix='conzfc_round16_') as td:
  temp=Path(td);work=temp/'packet';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));out=temp/'outputs';out.mkdir()
  # Preserve any caller-supplied audit hook in PYTHONPATH; never defeat isolation.
  env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
  def run(label,args,opt=False):
   cmd=[sys.executable]+(['-O'] if opt else [])+list(map(str,args));start=time.monotonic()
   p=subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   require(p.returncode==0,label+' failed:\n'+p.stdout[-20000:]);r['commands'].append({'name':label,'optimized':opt,'seconds':round(time.monotonic()-start,3),'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest()});print('PASS '+label+(' [-O]' if opt else ''),flush=True);return p.stdout
  def same(actual,expected,label):
   require(actual.is_file() and expected.is_file(),'Missing rebuilt file '+label);require(actual.read_bytes()==expected.read_bytes(),'Byte mismatch '+label);r['byte_equalities'].append({'file':label,'sha256':digest(actual),'bytes':actual.stat().st_size})
  for opt in modes:
   tag='optimized' if opt else 'normal';o=out/tag;o.mkdir()
   for script in ['build.py','build_two.py','build_two_weak.py']:
    run('scalar '+script,['scalar/'+script,'--check'],opt)
   for script in ['check.py','two_root/check.py','two_root_weak/check.py']:
    run('scalar '+script,['scalar/'+script],opt)
   run('source34 six coefficient recipes',['scalar/verify_coefficients.py'],opt)
   run('independent scalar product audit',['scalar_audit/audit_product.py'],opt)
   run('positive graph regeneration',['positive/build.py','--check'],opt)
   run('positive definition and degree audit',['positive/verify.py','--output',o/'positive.json'],opt)
   run('compact44 complete coefficient recipe',['positive/coefficients/recipe_compact44.py'],opt)
   run('independent small-equation algebra',['small_audit/check_small.py'],opt)
   run('natural composition and full expansions',['architecture/check_unified_cap.py','architecture/unified_cap_h12','architecture/unified_cap_sparse_h12','--output',o/'natural.json'],opt)
   run('natural byte-exact regeneration',['architecture/reproduce_unified_cap.py','--output',o/'natural-rebuild.json'],opt)
   ar=json.loads((o/'natural-rebuild.json').read_text());require(ar['status']=='passed' and len(ar['byte_exact_artifacts'])==26,'Natural rebuild file census')
   r['byte_equalities'].extend({'file':z['file']+' '+tag,'sha256':z['sha256'],'scope':'independently compared by natural reproducer'} for z in ar['byte_exact_artifacts'])
   projection=list((work/'architecture/portable/source').rglob('psd_contract/check.py'));require(len(projection)==1,'Unique natural projection checker')
   for name in ['unified_cap_h12','unified_cap_sparse_h12']:
    target=o/(name+'-projection');shutil.copytree(work/'architecture'/name/'natural',target)
    run('natural exact projection '+name,[projection[0],work/'architecture'/name/'raw/equation.json',target],opt)
   run('natural cap corruption controls',['architecture/check_cap_variants.py','architecture/unified_cap_h12/raw/raw_audit_input.json','--adversarial','--output',o/'cap-controls.json'],opt)
   for sparse,source,end in [(False,'cap_cofinal_self','integer324'),(True,'cap_sparse','integer338')]:
    stages=o/source;endpoint=o/end
    args=['direct/build_cap.py','direct/portable_input',stages,'--strong-cap','--odd-frame','--odd-comparison','--ys-only','--cofinal','--self-radix']+(['--sparse'] if sparse else [])
    run('signed source rebuild '+source,args,opt)
    for f in sorted((ROOT/'direct'/source).glob('*.json')):same(stages/f.name,f,'direct/'+source+'/'+f.name+' '+tag)
    run('signed exact centering '+end,['direct/center_integer.py',stages,endpoint],opt)
    for f in sorted((ROOT/'direct'/end).glob('*.json')):same(endpoint/f.name,f,'direct/'+end+'/'+f.name+' '+tag)
   run('independent signed chain and corruption controls',['cap_audit/check_compiled_cap.py','direct/cap_cofinal_self','direct/cap_sparse','--centered','direct/integer324','direct/integer338','--raw','direct/portable_input','--adversarial','--output',o/'signed.json'],opt)
   run('signed bounded-index controls',['cap_audit/check_signed_cap.py'],opt)
   run('odd anchor controls',['cap_audit/check_odd_anchor.py'],opt)
   run('complete proof text fidelity',['report_audit/check_proof_fidelity.py'],opt)
  r.update(status='PASS',temporary_copy_replay=True,commands_passed=len(r['commands']),byte_equalities_passed=len(r['byte_equalities']),elapsed_seconds=round(time.monotonic()-begin,3))
 text=json.dumps(r,indent=2)+'\n'
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(text)
 print(text)
if __name__=='__main__':main()
