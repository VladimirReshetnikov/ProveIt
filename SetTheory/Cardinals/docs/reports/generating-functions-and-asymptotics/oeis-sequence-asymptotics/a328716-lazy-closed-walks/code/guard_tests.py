#!/usr/bin/env python3
"""Corruption, syntax, and non-destructive regeneration guards, active under -O."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT/'code'))
import verify


def need(condition, message):
    if not condition:
        raise ValueError(message)


def run(flags,arguments,script='code/verify.py'):
    return subprocess.run([sys.executable,'-I','-S','-B',*flags,str(ROOT/script),*arguments],
                          cwd=ROOT,text=True,capture_output=True,shell=False,timeout=180)


def main():
    expected = verify.derive()
    verify.same(expected,verify.load_certificate(ROOT/'data/certificates.json'))
    verify.manuscript_prefix(ROOT/'Report179.tex')
    rejected = []
    def bad(label, callback):
        try:
            callback()
        except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError):
            rejected.append(label)
            return
        raise ValueError('expected rejection did not occur: '+label)
    mutants = []
    def add(label, edit):
        value = copy.deepcopy(expected)
        edit(value)
        mutants.append((label,json.dumps(value)))
    for k in range(1,4):
        add('relative c'+str(k),lambda d,k=k:d['relative_coefficients'][k][0].__setitem__('coefficient','0'))
        add('probability Q'+str(k),lambda d,k=k:d['probability_coefficients'][k][0].__setitem__('coefficient','0'))
    for k in (0,1,7):
        add('cumulant '+str(k+1),lambda d,k=k:d['cumulants'][k][0].__setitem__('coefficient','0'))
    add('OEIS term',lambda d:d['oeis_terms'].__setitem__(19,0))
    add('Riccati count',lambda d:d['count_cases'][-1].__setitem__('count',0))
    add('missing count case',lambda d:d['count_cases'].pop())
    add('joint count',lambda d:d['joint_cases'][-1].__setitem__('total',0))
    add('joint mean',lambda d:d['joint_cases'][-1].__setitem__('occupation_mean','0'))
    add('joint variance',lambda d:d['joint_cases'][-1].__setitem__('occupation_variance','0'))
    add('scope overclaim',lambda d:d['scope'].__setitem__('numerical_remainder_bounds_certified',True))
    add('wrong basis',lambda d:d['ring_variables'].__setitem__(0,'r'))
    add('noncanonical rational',lambda d:d['relative_coefficients'][0][0].__setitem__('coefficient','2/2'))
    add('float count',lambda d:d['oeis_terms'].__setitem__(0,1.0))
    add('boolean count',lambda d:d['oeis_terms'].__setitem__(0,True))
    add('boolean schema',lambda d:d.__setitem__('schema_version',True))
    add('false report',lambda d:d.__setitem__('report',178))
    add('missing field',lambda d:d.pop('cumulants'))
    add('extra field',lambda d:d.__setitem__('unexpected',0))
    add('diagnostic precision',lambda d:d['numerical_diagnostics'].__setitem__('precision_decimal_digits',53))
    add('diagnostic value',lambda d:d['numerical_diagnostics'].__setitem__('r','0.8'))
    add('reference digest',lambda d:d['reference_sha256'].__setitem__('data/walk_checks.json','0'*64))
    mutants += [('duplicate JSON key','{"report":179,'+json.dumps(expected)[1:]),
                ('NaN','{"x":NaN}'),('Infinity','{"x":Infinity}'),
                ('invalid JSON','{'),('wrong top-level type','[]')]
    manuscript = (ROOT/'Report179.tex').read_text()
    begin, end = '% BEGIN VERIFIED OEIS PREFIX','% END VERIFIED OEIS PREFIX'
    body = manuscript.split(begin,1)[1].split(end,1)[0]
    bad_tex = []
    target = str(verify.KNOWN[-1])
    for label, replacement in [('wrong term',str(verify.KNOWN[-1]+1)),
                               ('arithmetic term',target+'+0'),
                               ('decimal term',target+'.0'),
                               ('macro term',r'\num{'+target+'}'),
                               ('negative term','-'+target)]:
        altered = body.replace(target,replacement)
        need(altered != body,'mutation target missing')
        bad_tex.append((label,manuscript.replace(body,altered,1)))
    bad_tex += [('missing marker',manuscript.replace(begin,'prefix')),
                ('duplicate marker',manuscript+'\n'+begin),
                ('reversed markers',manuscript.replace(begin,'TEMP').replace(end,begin).replace('TEMP',end)),
                ('missing delimiter',manuscript.replace(body,body.replace(r'\]',''),1))]
    with tempfile.TemporaryDirectory(prefix='report179-corruption-') as temp:
        root = Path(temp)
        damaged = root/'damaged.json'
        for label,text in mutants:
            damaged.write_text(text)
            bad(label,lambda:verify.same(verify.load_certificate(damaged),expected))
        for label,text in bad_tex:
            damaged.write_text(text)
            bad(label,lambda:verify.manuscript_prefix(damaged))
        for expression in ('True','1.0','b.__class__','__import__("os")','b[0]',
                           '[1]','b**65','b**v','b//2','b%2','b if 1 else v'):
            bad('unsafe expression '+expression,lambda expression=expression:verify.expression(expression))
        link = root/'link.json'
        link.symlink_to(ROOT/'data/certificates.json')
        parent = root/'parent'
        parent.symlink_to(root,target_is_directory=True)
        for label,path in [('symlink input',link),('symlink parent',parent/'damaged.json'),
                           ('missing input',root/'missing'),('directory input',root)]:
            bad(label,lambda path=path:verify.load_certificate(path))
        if hasattr(os,'mkfifo'):
            os.mkfifo(root/'fifo')
            bad('FIFO input',lambda:verify.load_certificate(root/'fifo'))
        refs = root/'reference-fixture'
        (refs/'data').mkdir(parents=True)
        for name in verify.PINS:
            (refs/name).write_bytes((ROOT/name).read_bytes())
        with mock.patch.object(verify,'ROOT',refs):
            verify.references()
            (refs/'data/walk_checks.json').write_text('{}')
            bad('modified pinned reference',verify.references)
        outputs = []
        for index,flags in enumerate(([],['-O'])):
            positive = run(flags,[])
            need(positive.returncode==0,'CLI verifier failed: '+positive.stderr)
            outputs.append(positive.stdout)
            damaged.write_text(mutants[0][1])
            negative = run(flags,['--data',str(damaged)])
            need(negative.returncode==1 and 'VERIFICATION FAILED:' in negative.stderr,'CLI corruption accepted')
            rejected.append('CLI corruption mode '+str(index))
            regenerated = root/('regenerated'+str(index)+'.json')
            proc = run(flags,['--output',str(regenerated),'--compare',str(ROOT/'data/certificates.json')],'code/regenerate.py')
            need(proc.returncode==0,'regeneration failed: '+proc.stderr)
            before = regenerated.read_bytes()
            need(before==(ROOT/'data/certificates.json').read_bytes(),'regenerated bytes differ')
            proc = run(flags,['--output',str(regenerated)],'code/regenerate.py')
            need(proc.returncode==1 and regenerated.read_bytes()==before,'regenerator replaced output')
            rejected.append('existing regeneration output mode '+str(index))
            proc = run(flags,['--output',str(parent/'forbidden.json')],'code/regenerate.py')
            need(proc.returncode==1 and not (root/'forbidden.json').exists(),'regenerator followed parent symlink')
            rejected.append('symlink regeneration parent mode '+str(index))
    need(outputs[0]==outputs[1],'normal and optimized verifier differ')
    print(json.dumps({'status':'PASS','report':179,'all_guard_tests_passed':True,
                      'corrupt_certificates':len(mutants),'corrupt_manuscripts':len(bad_tex),
                      'total_negative_rejections':len(rejected),'positive_cli_runs':['normal','optimized (-O)'],
                      'regeneration_byte_identical':True,'normal_optimized_output_identical':True},sort_keys=True))

if __name__ == '__main__':
    try: main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError,subprocess.TimeoutExpired) as exc:
        print('GUARD TEST FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
