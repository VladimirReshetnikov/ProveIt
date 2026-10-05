#!/usr/bin/env python3
"""Finite-check corruption and non-destructive regeneration guards, also under -O."""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT/'code'))
import exact
import verify


def need(condition,message):
    if not condition:
        raise ValueError(message)


def run(flags,arguments,script='code/verify.py'):
    return subprocess.run([sys.executable,'-I','-S','-B',*flags,str(ROOT/script),*arguments],
                          cwd=ROOT,text=True,capture_output=True,shell=False,timeout=300)


def main():
    expected=verify.derive()
    verify.same(expected,verify.load_certificate(ROOT/'data/certificates.json'))
    verify.manuscript_prefix(ROOT/'Report181.tex')
    rejected=[]
    def bad(label,callback):
        try:
            callback()
        except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError):
            rejected.append(label)
            return
        raise ValueError('expected rejection did not occur: '+label)
    mutants=[]
    def add(label,edit):
        value=copy.deepcopy(expected)
        edit(value)
        mutants.append((label,json.dumps(value)))
    for n in (0,1,18,38,100,300,599,600):
        add('coefficient '+str(n),lambda d,n=n:d['coefficients_0_through_600'].__setitem__(n,-1))
    for n in range(19):
        add('composition '+str(n),lambda d,n=n:d['composition_counts_0_through_18'].__setitem__(n,-1))
    for n in range(10):
        add('h '+str(n+1),lambda d,n=n:d['h_1_through_h_10'].__setitem__(n,'0'))
    for key in ('E1','E2'):
        for n in range(len(expected[key])):
            add(key+' coefficient '+str(n),lambda d,n=n,key=key:d[key][n].__setitem__('coefficient','0'))
        for field,value in [('b_power',0),('gaussian_degree',0),('weighted_degree',0),('cumulant_powers',[0])]:
            add(key+' '+field,lambda d,key=key,field=field,value=value:d[key][0].__setitem__(field,value))
    for key in ('E1_leading','E2_leading','free_energy','constant_order_identity'):
        for n in range(len(expected[key]['terms'])):
            add(key+' term '+str(n),lambda d,key=key,n=n:d[key]['terms'][n].__setitem__('coefficient','0'))
        add(key+' basis',lambda d,key=key:d[key]['basis'].__setitem__(0,'wrong'))
    add('MacMahon coefficient',lambda d:d['free_energy']['MacMahon_positive_coefficients'].__setitem__('10','0'))
    add('log normalization',lambda d:d['free_energy']['separate_terms'].__setitem__(0,'-log(t)/6'))
    add('scope overclaim',lambda d:d['scope'].__setitem__('asymptotic_remainders_certified_by_code',True))
    add('finite monotonicity',lambda d:d.__setitem__('finite_strict_increase_a1_through_a600',False))
    add('reference pin',lambda d:d['reference_sha256'].__setitem__(next(iter(verify.PINS)),'0'*64))
    add('noncanonical rational',lambda d:d['h_1_through_h_10'].__setitem__(0,'2/2'))
    add('float count',lambda d:d['coefficients_0_through_600'].__setitem__(0,1.0))
    add('boolean count',lambda d:d['coefficients_0_through_600'].__setitem__(0,True))
    add('boolean schema',lambda d:d.__setitem__('schema_version',True))
    add('false report',lambda d:d.__setitem__('report',180))
    add('missing field',lambda d:d.pop('E2'))
    add('extra field',lambda d:d.__setitem__('unexpected',0))
    mutants += [('duplicate key','{"report":181,'+json.dumps(expected)[1:]),
                ('nested duplicate','{"a":{"b":1,"b":2}}'),
                ('NaN','{"x":NaN}'),('Infinity','{"x":Infinity}'),
                ('invalid JSON','{'),('wrong type','[]')]
    manuscript=(ROOT/'Report181.tex').read_text()
    begin,end='% BEGIN VERIFIED OEIS PREFIX','% END VERIFIED OEIS PREFIX'
    body=manuscript.split(begin,1)[1].split(end,1)[0]
    bad_tex=[]
    target=str(verify.KNOWN[-1])
    for label,replacement in [('wrong term',str(verify.KNOWN[-1]+1)),('arithmetic term',target+'+0'),
                              ('decimal term',target+'.0'),('macro term',r'\num{'+target+'}'),
                              ('negative term','-'+target),('leading zero','0'+target)]:
        altered=body.replace(target,replacement)
        need(altered!=body,'manuscript mutation target missing')
        bad_tex.append((label,manuscript.replace(body,altered,1)))
    bad_tex += [('missing marker',manuscript.replace(begin,'prefix')),
                ('duplicate marker',manuscript+'\n'+begin),
                ('reversed marker',manuscript.replace(begin,'TEMP').replace(end,begin).replace('TEMP',end)),
                ('missing delimiter',manuscript.replace(body,body.replace(r'\]',''),1))]
    with tempfile.TemporaryDirectory(prefix='report181-corruption-') as temp:
        root=Path(temp);damaged=root/'damaged.json'
        for label,text in mutants:
            damaged.write_text(text)
            bad(label,lambda:verify.same(verify.load_certificate(damaged),expected))
        for label,text in bad_tex:
            damaged.write_text(text)
            bad(label,lambda:verify.manuscript_prefix(damaged))
        data=(ROOT/'data/references/exact_terms_0_600.txt').read_text()
        for label,text in [('missing row','\n'.join(data.splitlines()[:-1])+'\n'),
                          ('wrong index',data.replace('600 ','601 ')),
                          ('decimal',data.replace('0 1\n','0 1.0\n')),
                          ('negative',data.replace('0 1\n','0 -1\n')),
                          ('double space',data.replace('0 1\n','0  1\n')),
                          ('leading zero',data.replace('0 1\n','0 01\n')),
                          ('trailing newline',data+'\n')]:
            damaged.write_text(text)
            bad('frozen syntax '+label,lambda:verify.frozen_terms(damaged))
        for function in (exact.product_coefficients,exact.composition_count,exact.formal_h):
            for arg in (-1,True,1.0,'1'):
                bad('invalid degree '+function.__name__+' '+repr(arg),lambda function=function,arg=arg:function(arg))
        bad('zero Edgeworth order',lambda:exact.edgeworth_tuples(0))
        bad('nonzero logarithm constant',lambda:exact.series_log_one_plus([exact.Q(1),exact.Q(0)],1))
        bad('unequal series lengths',lambda:exact.series_mul([exact.Q(1)],[exact.Q(1),exact.Q(0)],1))
        bad('invalid zeta parity',lambda:exact.zeta_negative_odd(2))
        # Finite formal truncations must agree in their overlapping degrees.
        need(exact.formal_h(8)==exact.formal_h(10)[:9],'formal truncations disagree')
        link=root/'link.json';link.symlink_to(ROOT/'data/certificates.json')
        parent=root/'parent';parent.symlink_to(root,target_is_directory=True)
        for label,path in [('symlink input',link),('symlink parent',parent/'damaged.json'),
                           ('missing input',root/'missing'),('directory input',root)]:
            bad(label,lambda path=path:verify.load_certificate(path))
        if hasattr(os,'mkfifo'):
            os.mkfifo(root/'fifo')
            bad('FIFO input',lambda:verify.load_certificate(root/'fifo'))
        refs=root/'reference-fixture'
        for name in verify.PINS:
            (refs/name).parent.mkdir(parents=True,exist_ok=True)
            (refs/name).write_bytes((ROOT/name).read_bytes())
        with mock.patch.object(verify,'ROOT',refs):
            verify.references()
            (refs/'data/references/exact_terms_0_600.txt').write_text('0 0\n')
            bad('modified frozen reference',verify.references)
        outputs=[]
        for index,flags in enumerate(([],['-O'])):
            positive=run(flags,[])
            need(positive.returncode==0,'CLI verifier failed: '+positive.stderr)
            outputs.append(positive.stdout)
            damaged.write_text(mutants[0][1])
            negative=run(flags,['--data',str(damaged)])
            need(negative.returncode==1 and 'VERIFICATION FAILED:' in negative.stderr,'CLI corruption accepted')
            rejected.append('CLI corruption mode '+str(index))
            regenerated=root/('regenerated'+str(index)+'.json')
            proc=run(flags,['--output',str(regenerated),'--compare',str(ROOT/'data/certificates.json')],'code/regenerate.py')
            need(proc.returncode==0,'regeneration failed: '+proc.stderr)
            before=regenerated.read_bytes()
            need(before==(ROOT/'data/certificates.json').read_bytes(),'regenerated bytes differ')
            proc=run(flags,['--output',str(regenerated)],'code/regenerate.py')
            need(proc.returncode==1 and regenerated.read_bytes()==before,'regenerator overwrote output')
            rejected.append('existing regeneration output mode '+str(index))
            proc=run(flags,['--output',str(parent/'forbidden.json')],'code/regenerate.py')
            need(proc.returncode==1 and not (root/'forbidden.json').exists(),'regenerator followed parent symlink')
            rejected.append('symlink regeneration parent mode '+str(index))
    need(outputs[0]==outputs[1],'normal and optimized verifier differ')
    print(json.dumps({'status':'PASS','report':181,'all_guard_tests_passed':True,
                      'corrupt_certificates':len(mutants),'corrupt_manuscripts':len(bad_tex),
                      'total_negative_rejections':len(rejected),'positive_cli_runs':['normal','optimized (-O)'],
                      'regeneration_byte_identical':True,'normal_optimized_output_identical':True},sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError,subprocess.TimeoutExpired) as exc:
        print('GUARD TEST FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
