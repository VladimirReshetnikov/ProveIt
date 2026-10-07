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
    verify.manuscript_prefix(ROOT/'Report180.tex')
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
    for key,order in [('scalar_corrections',6),('marked_corrections',6),('PGF_multipliers',4)]:
        for k in range(1,order+1):
            add(key+' '+str(k),lambda d,key=key,k=k:d[key][k][0].__setitem__('coefficient','0'))
    for key in ('H_coefficients','G_coefficients','L_coefficients','cotangent_coefficients'):
        add(key,lambda d,key=key:next(v for v in reversed(d[key]) if v)[0].__setitem__('coefficient','0'))
    add('OEIS term',lambda d:d['oeis_terms'].__setitem__(20,0))
    add('count case',lambda d:d['count_cases'][-1].__setitem__('count',0))
    add('missing count case',lambda d:d['count_cases'].pop())
    add('marked diagonal',lambda d:d['marked_cases'][-1]['diagonal'][0].__setitem__('coefficient','0'))
    add('Sturm count',lambda d:d['n10_sturm'].__setitem__('real_root_count',8))
    add('Sturm coefficient',lambda d:d['n10_sturm']['chain_coefficients_ascending'][0].__setitem__(0,'0'))
    add('Sturm sign',lambda d:d['n10_sturm']['signs_minus_infinity'].__setitem__(0,-1))
    add('tail bound',lambda d:d['certificate_tails'].__setitem__('wronskian_tail_bound','0'))
    add('enclosure rounding',lambda d:d['published_amplitude_enclosure'].__setitem__(0,'26'))
    add('scope overclaim',lambda d:d['scope'].__setitem__('finite_N_asymptotic_remainders_certified',True))
    add('wrong basis',lambda d:d['ring_variables'].__setitem__(0,'rho'))
    add('noncanonical rational',lambda d:d['scalar_corrections'][0][0].__setitem__('coefficient','2/2'))
    add('float count',lambda d:d['oeis_terms'].__setitem__(0,1.0))
    add('boolean count',lambda d:d['oeis_terms'].__setitem__(0,True))
    add('boolean schema',lambda d:d.__setitem__('schema_version',True))
    add('false report',lambda d:d.__setitem__('report',179))
    add('missing field',lambda d:d.pop('H_coefficients'))
    add('extra field',lambda d:d.__setitem__('unexpected',0))
    add('reference digest',lambda d:d['reference_sha256'].__setitem__('data/references/checks.json','0'*64))
    mutants += [('duplicate JSON key','{"report":180,'+json.dumps(expected)[1:]),
                ('NaN','{"x":NaN}'),('Infinity','{"x":Infinity}'),
                ('invalid JSON','{'),('wrong top-level type','[]')]
    manuscript = (ROOT/'Report180.tex').read_text()
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
    with tempfile.TemporaryDirectory(prefix='report180-corruption-') as temp:
        root = Path(temp)
        damaged = root/'damaged.json'
        for label,text in mutants:
            damaged.write_text(text)
            bad(label,lambda:verify.same(verify.load_certificate(damaged),expected))
        for label,text in bad_tex:
            damaged.write_text(text)
            bad(label,lambda:verify.manuscript_prefix(damaged))
        for expression in ('True','1.0','lam.__class__','__import__("os")','lam[0]',
                           '[1]','lam**65','lam**r','lam//2','lam%2','lam if 1 else r','r','r**3','1/lam'):
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
            (refs/name).parent.mkdir(parents=True,exist_ok=True)
            (refs/name).write_bytes((ROOT/name).read_bytes())
        with mock.patch.object(verify,'ROOT',refs):
            verify.references()
            (refs/'data/references/checks.json').write_text('{}')
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
    print(json.dumps({'status':'PASS','report':180,'all_guard_tests_passed':True,
                      'corrupt_certificates':len(mutants),'corrupt_manuscripts':len(bad_tex),
                      'total_negative_rejections':len(rejected),'positive_cli_runs':['normal','optimized (-O)'],
                      'regeneration_byte_identical':True,'normal_optimized_output_identical':True},sort_keys=True))

if __name__ == '__main__':
    try: main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError,subprocess.TimeoutExpired) as exc:
        print('GUARD TEST FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
