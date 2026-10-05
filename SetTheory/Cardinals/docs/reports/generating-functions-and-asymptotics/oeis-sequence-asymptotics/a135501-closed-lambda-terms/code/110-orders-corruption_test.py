#!/usr/bin/env python3
"""Reject deliberate corruption in disposable copies, normal and optimized.
Mathematical mutations bypass integrity.py so hashes cannot hide dead guards.
"""
from hashlib import sha256
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def replace(root,old,new):
    p=root/'check.py'; text=p.read_text()
    require(text.count(old)==1,'ambiguous mutation target '+old)
    p.write_text(text.replace(old,new,1))

def fixture(root,kind):
    p=root/'data/counts.json'
    if kind=='missing':
        p.unlink(); return
    if kind=='extra':
        (root/'data/extra.json').write_text('{}'); return
    if kind=='nested':
        (root/'data/nested').mkdir(); return
    if kind=='malformed':
        p.write_text('{not JSON'); return
    if kind=='duplicate':
        p.write_text(p.read_text().replace('{','{"0": [],',1)); return
    obj=json.loads(p.read_text())
    if kind=='tail': obj['0'][-1][1]+=1
    elif kind=='truncated': obj['0'].pop()
    elif kind=='boolean': obj['0'][1][1]=True
    elif kind=='coefficient':
        p=root/'data/coefficients.json'; obj=json.loads(p.read_text()); obj['P'][5][-1]='0'
    elif kind=='summary':
        p=root/'data/check_results.json'; obj=json.loads(p.read_text()); obj['total_checks']+=1
    else: raise RuntimeError('unknown fixture case')
    p.write_text(json.dumps(obj))

def main():
    for optimized in (False,True):
        for entry in ('integrity.py','check.py'):
            command=[sys.executable]+(['-O'] if optimized else [])+[entry]
            cp=subprocess.run(command,cwd=ROOT,text=True,capture_output=True)
            require(cp.returncode==0,'pristine preflight failed '+entry+' '+cp.stderr)
    manifest=json.loads((ROOT/'manifest.json').read_text())
    names=sorted(manifest['files'])+['manifest.json']
    before={name:sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    cases=[]
    logic=[
      ('direct unary','value+=direct(m+1,u-1,b)','value+=direct(m,u-1,b)','size recurrence or parity'),
      ('size parity','if (N-u)%r==0)','if (N-u)%r!=0)','size recurrence or parity'),
      ('zero-cost variables','value=m if n==s else 0','value=m if n==1 else 0','size recurrence or parity'),
      ('shape height','max(h1,h2)]+=v1*v2','min(h1,h2)]+=v1*v2','explicit and DP shapes'),
      ('explicit tree height','h=max(leaves); d=u-h','h=min(leaves); d=u-h','tree structure'),
      ('coarse radical','F(u**(2*u-1),factorial(u)**2)','F(u**(2*u-1),2*factorial(u)**2)','coarse radical bound'),
      ('height radical','delta**(-2*d)','delta**(-2*d)/2','height radical bound'),
      ('reduced radical','comb(2*j,j)*m**j*numerator[b-j]','comb(2*j,j)*(m+1)**j*numerator[b-j]','direct and reduced recurrence'),
      ('spine convolution','cat(b)*u**(b+1)*partial','cat(b)*u**(b+2)*partial','Catalan convolution'),
      ('probability mean','F(u,2)*(harmonic-1)','F(u,3)*(harmonic-1)','negative binomial mean'),
      ('forward log sign','coefficient=slog(U,d)[j]','coefficient=ps(slog(U,d)[j],-1)','forward residual'),
      ('inverse quadratic','core[2]=pa(core[2],ONE)','core[2]=pa(core[2],ps(ONE,2))','inverse residual'),
      ('printed coefficient','F(-77,60)','F(-76,60)','printed forward coefficients'),
    ]
    # The inverse quadratic token occurs in two contexts, so target its complete line.
    logic[11]=('inverse quadratic',
      'if d>=2: core[2]=pa(core[2],ONE)',
      'if d>=2: core[2]=pa(core[2],ps(ONE,2))','inverse residual')
    for label,old,new,diagnostic in logic:
        cases.append(('logic '+label,'check.py',lambda root,o=old,n=new:replace(root,o,n),diagnostic))
    for kind in ('missing','extra','nested','malformed','duplicate','tail','truncated','boolean','coefficient','summary'):
        cases.append(('fixture '+kind,'check.py',lambda root,k=kind:fixture(root,k),None))
    def damage(root,name):
        p=root/name;p.write_bytes(p.read_bytes()+b'\nCORRUPTED\n')
    for name in ('report110.tex','report110.pdf','check.py','data/coefficients.json'):
        cases.append(('integrity bytes '+name,'integrity.py',lambda root,n=name:damage(root,n),'integrity mismatch: '+name))
    cases.append(('integrity extra','integrity.py',lambda root:(root/'extra.txt').write_text('extra'),'inventory mismatch'))
    cases.append(('integrity missing','integrity.py',lambda root:(root/'report110.pdf').unlink(),'inventory mismatch'))
    def manifest_mutation(root,kind):
        p=root/'manifest.json';obj=json.loads(p.read_text())
        if kind=='duplicate': p.write_text(p.read_text().replace('{','{"schema":1,',1));return
        if kind=='schema boolean':obj['schema']=True
        elif kind=='size boolean':obj['files']['report110.tex']['size_bytes']=True
        elif kind=='unsafe path':obj['files']['../escape.txt']=obj['files'].pop('report110.tex')
        elif kind=='nested build':
            p=root/'data/build/extra.txt';p.parent.mkdir();p.write_text('extra');return
        p.write_text(json.dumps(obj))
    for kind in ('duplicate','schema boolean','size boolean','unsafe path','nested build'):
        cases.append(('manifest '+kind,'integrity.py',lambda root,k=kind:manifest_mutation(root,k),None))
    results=[]
    with tempfile.TemporaryDirectory(prefix='report110-corruption-') as tmp:
        for index,(label,entry,mutation,diagnostic) in enumerate(cases):
            root=Path(tmp)/str(index);root.mkdir()
            for name in names:
                dest=root/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,dest)
            mutation(root)
            for optimized in (False,True):
                command=[sys.executable]+(['-O'] if optimized else [])+[entry]
                cp=subprocess.run(command,cwd=root,text=True,capture_output=True)
                require(cp.returncode!=0,'CORRUPTION ESCAPED '+label)
                require('RuntimeError:' in cp.stderr,'not explicit guard '+label+' '+cp.stderr)
                if diagnostic:
                    require('RuntimeError: '+diagnostic in cp.stderr,'wrong diagnostic '+label+' '+cp.stderr)
                require('SyntaxError:' not in cp.stderr,'invalid source mutant '+label)
                results.append({'case':label,'optimized':optimized,'rejected':True})
    after={name:sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    require(before==after,'original payload changed during corruption campaign')
    print(json.dumps({'status':'PASS','mutation_cases':len(cases),
      'pristine_normal_and_optimized_preflights':True,'original_files_hashed':len(names),
      'normal_and_optimized_rejections':len(results),'originals_unchanged':True,'results':results},indent=2,sort_keys=True))

if __name__=='__main__': main()
