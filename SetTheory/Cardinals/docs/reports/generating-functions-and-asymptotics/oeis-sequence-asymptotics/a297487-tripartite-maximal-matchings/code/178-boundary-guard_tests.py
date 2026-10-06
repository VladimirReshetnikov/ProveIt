#!/usr/bin/env python3
"""Deliberately corrupt exact data and manuscript inputs in normal and -O modes."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent

def need(condition,message):
    if not condition:raise RuntimeError(message)

def run(flags,arguments,script='code/verify.py'):
    return subprocess.run([sys.executable,'-I','-B',*flags,str(ROOT/script),*arguments],cwd=ROOT,text=True,capture_output=True,shell=False,timeout=180)

def main():
    positives=[]
    for flags in ([],['-O']):
        proc=run(flags,[]);need(proc.returncode==0,'positive verifier failed: '+proc.stderr)
        result=json.loads(proc.stdout);need(result.get('status')=='PASS' and result.get('all_checks_passed') is True,'positive PASS missing')
        need(result.get('higher_order_checked')==6,'higher order check missing')
        positives.append(proc.stdout)
    need(positives[0]==positives[1],'normal and optimized outputs differ')
    original=json.loads((ROOT/'data/certificates.json').read_text())
    mutants=[]
    def add(label,edit):
        item=copy.deepcopy(original);edit(item);mutants.append((label,json.dumps(item)))
    add('relative c1',lambda d:d['boundary']['relative'][1].__setitem__(1,'0'))
    add('relative c4',lambda d:d['boundary']['relative'][4].__setitem__(1,'0'))
    add('phase h4',lambda d:d['boundary']['phase']['4'][0].__setitem__(0,'1'))
    add('log coefficient',lambda d:d['boundary']['log_relative'][2].__setitem__(2,'0'))
    add('mean insertion',lambda d:d['boundary']['mean_y'][4].__setitem__(0,'0'))
    add('variance insertion',lambda d:d['boundary']['variance_y'][4].__setitem__(2,'0'))
    add('factorial correction',lambda d:d['boundary']['log_A_n_inverse_n'].__setitem__(0,'-55/324'))
    add('sixth order coefficient',lambda d:d['higher_order_check']['relative'][6].__setitem__(0,'0'))
    add('sixth log coefficient',lambda d:d['higher_order_check']['log_relative'][6].__setitem__(0,'0'))
    for key in ('c1','c2','ell2','m0','v1','u','delta'):
        add('moving '+key,lambda d,key=key:d['moving'][0].__setitem__(key,'0'))
    add('missing moving point',lambda d:d['moving'].pop())
    add('exterior correction',lambda d:d['exterior'][0]['relative_coefficients'].__setitem__(1,'0'))
    add('exterior second correction',lambda d:d['exterior'][0]['relative_coefficients'].__setitem__(2,'0'))
    add('graph total',lambda d:d['integer_cases'][10].__setitem__('total',0))
    add('graph odd perfect',lambda d:d['integer_cases'][1].__setitem__('perfect',1))
    add('graph branch',lambda d:d['integer_cases'][10]['branches'].__setitem__(1,0))
    add('missing integer case',lambda d:d['integer_cases'].pop())
    add('last boundary count',lambda d:d['boundary']['counts_n0_to15'].__setitem__(15,0))
    add('noncanonical rational',lambda d:d['boundary']['relative'][1].__setitem__(1,'422/432'))
    add('float count',lambda d:d['boundary']['counts_n0_to15'].__setitem__(0,1.0))
    add('boolean count',lambda d:d['boundary']['counts_n0_to15'].__setitem__(0,True))
    add('boolean schema',lambda d:d.__setitem__('schema_version',True))
    add('wrong basis',lambda d:d['boundary']['basis'].__setitem__(1,'a^2'))
    add('scope overclaim',lambda d:d['scope'].__setitem__('numerical_remainder_bounds_certified',True))
    add('missing field',lambda d:d.pop('moving'))
    add('extra field',lambda d:d.__setitem__('extra',0))
    mutants += [('duplicate JSON key','{"report":178,'+json.dumps(original)[1:]),('nonfinite JSON','{"x":NaN,'+json.dumps(original)[1:]),('invalid JSON','{'),('wrong top-level type','[]')]
    manuscript=(ROOT/'Report178.tex').read_text()
    begin='% BEGIN VERIFIED BOUNDARY PREFIX';end='% END VERIFIED BOUNDARY PREFIX'
    need(manuscript.count(begin)==1 and manuscript.count(end)==1,'manuscript prefix markers missing')
    body=manuscript.split(begin,1)[1].split(end,1)[0]
    bad_tex=[]
    for label,replacement in [('wrong initial value',body.replace('19743705360','19743705361')),
        ('arithmetic value',body.replace('19743705360','19743705360+0')),
        ('decimal value',body.replace('19743705360','19743705360.0')),
        ('macro value',body.replace('19743705360',r'\num{19743705360}')),
        ('negative value',body.replace('19743705360','-19743705360')),
        ('short prefix',body.replace(',','',1)),
        ('missing display',body.replace(r'\]', ''))]:
        need(replacement!=body,'manuscript mutation did not change target')
        bad_tex.append((label,manuscript.replace(body,replacement,1)))
    bad_tex += [('missing marker',manuscript.replace(begin,'Initial values')),
                ('duplicate marker',manuscript+'\n'+begin),('reversed markers',manuscript.replace(begin,'TEMP').replace(end,begin).replace('TEMP',end))]
    rejected=0
    with tempfile.TemporaryDirectory(prefix='report178-corruption-') as tmp:
        root=Path(tmp);bad=root/'bad.json'
        for label,content in mutants:
            bad.write_text(content)
            for flags in ([],['-O']):
                result=run(flags,['--data',str(bad)])
                need(result.returncode==1 and 'VERIFICATION FAILED:' in result.stderr,label+' accepted: '+result.stdout+result.stderr);rejected+=1
        for label,content in bad_tex:
            bad.write_text(content)
            for flags in ([],['-O']):
                result=run(flags,['--manuscript',str(bad)])
                need(result.returncode==1 and 'VERIFICATION FAILED:' in result.stderr,label+' accepted: '+result.stdout+result.stderr);rejected+=1
        bad.unlink()
        link=root/'link.json';link.symlink_to(ROOT/'data/certificates.json')
        missing=root/'missing.json'
        for label,path in [('missing certificate',missing),('symlink certificate',link),('directory certificate',root)]:
            for flags in ([],['-O']):
                result=run(flags,['--data',str(path)])
                need(result.returncode==1 and 'VERIFICATION FAILED:' in result.stderr,label+' accepted');rejected+=1
        # Regeneration is exact and non-destructive, including symlink parents.
        for index,flags in enumerate(([],['-O'])):
            output=root/('regenerated'+str(index)+'.json')
            result=run(flags,['--output',str(output),'--compare',str(ROOT/'data/certificates.json')],'code/regenerate.py')
            need(result.returncode==0,'regeneration failed '+result.stderr)
            before=output.read_bytes();need(before==(ROOT/'data/certificates.json').read_bytes(),'regenerated bytes differ')
            result=run(flags,['--output',str(output)],'code/regenerate.py')
            need(result.returncode==1 and output.read_bytes()==before,'regeneration overwrote existing output');rejected+=1
            parent_link=root/('parent'+str(index));parent_link.symlink_to(root,target_is_directory=True)
            result=run(flags,['--output',str(parent_link/'should-not-exist.json')],'code/regenerate.py')
            need(result.returncode==1 and not (root/'should-not-exist.json').exists(),'regeneration accepted symlink parent');rejected+=1
    print(json.dumps({'status':'PASS','report':178,'all_guard_tests_passed':True,'positive_runs':['normal','optimized (-O)'],'identical_positive_output':True,'corrupt_certificates_per_mode':len(mutants),'corrupt_manuscripts_per_mode':len(bad_tex),'total_negative_rejections':rejected,'regeneration_byte_identical':True},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,KeyError,TypeError,subprocess.TimeoutExpired) as exc:
        print('GUARD TEST FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
