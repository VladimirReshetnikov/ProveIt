#!/usr/bin/env python3
"""Selected adversarial regressions; run both ordinary and optimized Python."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
MEMBERS=('README.md','evidence.json','manifest.sha256','negative_tests.py','provenance.json','verify.py')

class Reject(Exception): pass

def need(test,message):
    if not test: raise Reject(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def encode(value): return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()

def snapshot(root):
    result={}
    for p in sorted(root.rglob('*')):
        s=p.lstat(); rel=str(p.relative_to(root))
        if stat.S_ISREG(s.st_mode): result[rel]=['file',sha(p.read_bytes())]
        elif stat.S_ISLNK(s.st_mode): result[rel]=['link',os.readlink(p)]
        elif stat.S_ISDIR(s.st_mode): result[rel]=['directory']
        else: result[rel]=['special',stat.S_IFMT(s.st_mode)]
    return result

def copy(destination):
    destination.mkdir()
    for name in MEMBERS: shutil.copyfile(HERE/name,destination/name)

def reseal(root):
    (root/'manifest.sha256').write_text(''.join(sha((root/name).read_bytes())+'  '+name+'\n' for name in MEMBERS if name!='manifest.sha256'))

def mutate_json(root,file,path,value=None,delete=False):
    obj=json.loads((root/file).read_text()); target=obj
    for key in path[:-1]: target=target[key]
    if delete: del target[path[-1]]
    else: target[path[-1]]=value
    (root/file).write_bytes(encode(obj))

def replace(root,old,new,file='verify.py'):
    p=root/file; data=p.read_text(); need(data.count(old)==1,'test mutation must have exactly one source target: '+old)
    p.write_text(data.replace(old,new))

def invoke(root,mode,output=None):
    command=[sys.executable]+(['-O'] if mode else [])+[str(root/'verify.py')]
    if output is not None: command+=['--output',str(output)]
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run(command,cwd=root.parent,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=90)

def mutations():
    tests=[]
    def data(name,path,value,code,file='evidence.json'):
        tests.append((name,lambda root:mutate_json(root,file,path,value),code,True))
    data('wrong potential correction',['constants','potential_correction'],'5/6','math:potential-correction')
    data('wrong action correction',['constants','action_correction'],'7/2','math:action-correction')
    data('wrong coefficient inverse',['constants','threshold_inverse_correction'],'2','math:threshold-inverse')
    data('wrong deficit inverse lead',['constants','inverse_lead_denominator'],'3','math:inverse-correction')
    data('wrong deficit inverse loglog',['constants','inverse_loglog'],'1','math:inverse-correction')
    data('wrong saddle lead',['constants','saddle_lead'],'9','math:saddle-correction')
    data('wrong saddle correction',['constants','saddle_second'],'0','math:saddle-correction')
    data('wrong moment loglog',['constants','moment_loglog'],'-1','math:moment-correction')
    data('wrong moment second',['constants','moment_second'],'0','math:moment-correction')
    data('old cap numerator two',['constants','cap_numerator'],'2','math:cap-four')
    data('wrong strip factor',['constants','strip_fraction'],'1','math:cap-four')
    data('wrong diffusion',['models','247','D'],'1/6','math:model')
    data('wrong alpha',['models','759','alpha'],'2','math:model')
    data('wrong boundary mass',['models','247','r'],'3/4','math:model')
    data('wrong anchored exponent',['rates','anchored_root'],'-1/6','math:rate-ledger')
    data('wrong clock exponent',['rates','clock_failure'],'-1/3','math:rate-ledger')
    data('wrong reward exponent',['rates','reward_failure'],'0','math:rate-ledger')
    data('wrong tube exponent',['rates','tube_margin'],'1/84','math:rate-ledger')
    data('wrong endpoint exponent',['rates','endpoint_cost_log'],'-6','math:rate-ledger')
    data('noncanonical rational',['constants','potential_base'],'2/6','schema:rational')
    data('float rational',['constants','potential_base'],1.0,'schema:rational')
    data('boolean rational',['constants','potential_base'],True,'schema:rational')
    data('boolean integer',['coverage','p_max'],True,'schema:integer')
    data('reduced height coverage',['coverage','p_max'],9,'coverage:p_max')
    data('reduced original time coverage',['coverage','n_max'],15,'coverage:n_max')
    data('reduced brute coverage',['coverage','brute_max'],6,'coverage:brute_max')
    data('reduced root iterations',['coverage','root_steps'],47,'coverage:root_steps')
    data('removed check',['checks'],['legal_transforms'],'schema:checks')
    data('unsupported analytic scope',['scope'],'uniform_asymptotic_certificate','schema:scope')
    data('extra top key',['extra'],0,'schema:top')
    data('extra nested key',['models','759','extra'],'0','schema:model')
    data('wrong analytic report',['analytic_report'],'Unspecified report','provenance:report','provenance.json')
    data('wrong primary source',['primary_source'],'https://example.invalid/source','provenance:source','provenance.json')
    data('external runtime dependency',['runtime_dependencies'],['old-checker.py'],'provenance:implementation','provenance.json')
    tests.append(('missing nested key',lambda root:mutate_json(root,'evidence.json',['rates','S'],delete=True),'schema:rates',True))
    tests.append(('duplicate JSON key',lambda root:replace(root,'"schema": 1','"schema": 1, "schema": 1','evidence.json'),'schema:duplicate-key',True))
    tests.append(('nonfinite JSON',lambda root:replace(root,'"schema": 1','"schema": NaN','evidence.json'),'schema:nonfinite',True))
    def source(name,old,new,code): tests.append((name,lambda root:replace(root,old,new),code,True))
    source('wrong legal cutoff','for ell in range(p):\n        for b in range(ell+1):\n            m=mult(j,ell,b)\n            if not m: continue\n            bulk=', 'for ell in range(p+1):\n        for b in range(ell+1):\n            m=mult(j,ell,b)\n            if not m: continue\n            bulk=', 'math:legal-row')
    source('wrong drift sign','slope=-ed/el; curvature=', 'slope=ed/el; curvature=', 'math:implicit-drift')
    source('wrong duration variance','var=F(b)*q/(1-q)**2','var=F(b)*q/(1-q)', 'math:joint-moments')
    source('unanchored sign','EY-D*LX**2/2','EY+D*LX**2/2','math:anchored-cancellation')
    source('wrong dual square','(1,-1,0):F(-2)','(1,-1,0):F(-1)','math:dual-square')
    source('wrong countdown count','found.get(w,0)==choose(w-1,b-1)','found.get(w,0)==choose(w,b-1)','math:first-return')
    source('wrong renewal original clock','range(b,N-t):\n                            end=p+w-ell; L=w+1','range(b,N-t-1):\n                            end=p+w-ell; L=w+2','math:genuine-time')
    source('wrong bridge sign','end,down=support(j,p+g,b,ell,ell-g)','end,down=support(j,p+g,b,ell,ell+g)','math:bridge-down')
    source('wrong exact filler sum','sum(length*num for length,num in runs)==U','sum(length*num for length,num in runs)==U+1','math:fill-exact')
    tests.append(('unsealed source change',lambda root:(root/'verify.py').write_text((root/'verify.py').read_text()+'\n# changed\n'),'manifest:digest',False))
    tests.append(('extra member',lambda root:(root/'surplus').write_text('x'),'inventory:members',False))
    tests.append(('missing member',lambda root:(root/'README.md').unlink(),'inventory:members',False))
    def directory(root): (root/'README.md').unlink();(root/'README.md').mkdir()
    tests.append(('directory member',directory,'inventory:regular',False))
    def symlink(root): (root/'README.md').unlink();(root/'README.md').symlink_to('evidence.json')
    tests.append(('symlink member',symlink,'inventory:regular',False))
    def fifo(root): (root/'README.md').unlink();os.mkfifo(root/'README.md')
    tests.append(('fifo member',fifo,'inventory:regular',False))
    tests.append(('truncated manifest',lambda root:(root/'manifest.sha256').write_text(''),'manifest:count',False))
    tests.append(('unsorted manifest',lambda root:(root/'manifest.sha256').write_text('\n'.join(reversed((root/'manifest.sha256').read_text().splitlines()))+'\n'),'manifest:format',False))
    return tests

def run():
    cases=[]; clean_hash=None
    with tempfile.TemporaryDirectory(prefix='report129-negative-') as temp:
        home=Path(temp)
        for index,(name,change,code,sealed) in enumerate(mutations()):
            root=home/('case-'+str(index));copy(root);change(root)
            if sealed: reseal(root)
            before=snapshot(root)
            for mode in (False,True):
                target=home/('result-'+str(index)+'-'+str(mode)+'.json')
                proc=invoke(root,mode,target)
                need(proc.returncode==1,'unexpected exit for '+name+': '+str(proc.returncode)+' '+proc.stderr.decode())
                need(proc.stderr==('FAIL '+code+'\n').encode(),'wrong diagnostic for '+name+': '+repr(proc.stderr))
                need(proc.stdout==b'' and not target.exists(),'unexpected result for '+name)
                need(snapshot(root)==before,'mutated sealed copy for '+name)
            cases.append({'case':name,'diagnostic':code,'modes':['normal','optimized'],'result':'rejected'})
        clean=[]
        for number in range(2):
            root=home/('clean-'+str(number));copy(root);before=snapshot(root)
            for mode in (False,True):
                proc=invoke(root,mode)
                need(proc.returncode==0 and proc.stderr==b'','clean replay failed '+proc.stderr.decode())
                need(snapshot(root)==before,'clean replay modified source')
                if clean_hash is None: clean_hash=sha(proc.stdout)
                need(sha(proc.stdout)==clean_hash,'normal/optimized or clean-copy bytes differ')
                clean.append({'copy':number,'mode':'optimized' if mode else 'normal','sha256':sha(proc.stdout),'unchanged':True})
        protections=[]
        root=home/'protected';copy(root)
        for mode in (False,True):
            for kind in ('inside-new','inside-existing','existing-outside','symlink-outside'):
                marker=home/('marker-'+str(mode)+'-'+kind);marker.write_bytes(b'unchanged marker')
                if kind=='inside-new': target=root/'new.json';code='output:sealed-directory'
                elif kind=='inside-existing': target=root/'evidence.json';code='output:sealed-directory'
                elif kind=='existing-outside': target=marker;code='output:exists'
                else:
                    target=home/('link-'+str(mode));target.symlink_to(marker);code='output:symlink'
                before=snapshot(root);proc=invoke(root,mode,target)
                need(proc.returncode==1 and proc.stdout==b'' and proc.stderr==('FAIL '+code+'\n').encode(),'output protection failed '+kind)
                need(snapshot(root)==before and marker.read_bytes()==b'unchanged marker','output protection changed content')
                if kind=='inside-new': need(not target.exists(),'created forbidden output')
                protections.append({'case':kind,'mode':'optimized' if mode else 'normal','diagnostic':code})
        return {'schema':1,'status':'PASS','scope':'selected_adversarial_regressions','mutations':cases,'mutation_count':len(cases),'rejected_runs':2*len(cases),'clean_replays':clean,'output_protections':protections,'clean_result_sha256':clean_hash}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output');args=parser.parse_args()
    try:
        if args.output:
            path=Path(args.output).absolute();resolved=path.resolve(strict=False)
            need(not path.is_symlink(),'output:symlink')
            need(HERE not in [resolved,*resolved.parents],'output:sealed-directory')
            need(not path.exists(),'output:exists')
        result=encode(run())
        if args.output:
            fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0),0o600)
            with os.fdopen(fd,'wb') as handle:handle.write(result)
        else:sys.stdout.buffer.write(result)
    except (Reject,OSError,ValueError,subprocess.TimeoutExpired) as exc:
        print('FAIL '+str(exc),file=sys.stderr);return 1
    return 0

if __name__=='__main__':sys.exit(main())
