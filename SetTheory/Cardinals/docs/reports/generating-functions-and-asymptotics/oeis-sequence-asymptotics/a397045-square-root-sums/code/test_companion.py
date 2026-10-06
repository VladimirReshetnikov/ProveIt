#!/usr/bin/env python3
"""Executable regression/adversarial checks, equally effective under python -O."""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import companion as c


def run_tests():
    passed = []
    def check(name, value):
        c.require(value, 'FAIL: '+name)
        passed.append(name)
    def rejected(name, call, exceptions=(ValueError, OSError)):
        try:
            call()
        except exceptions:
            passed.append(name)
            return
        raise c.ValidationError('FAIL: expected rejection: '+name)
    fixture = c.load_fixture()
    check('historical fixture intact through n35', len(fixture)==36 and fixture[35]==428363342)
    report = c.exact()
    check('fresh cumulative n20 vector total',report['cumulative_run']['vectors']==458000)
    check('fresh cumulative generator count',report['cumulative_run']['generators']==268)
    check('fresh independent direct shell total',report['direct_shell_run']['vectors']==14155)
    check('direct shells independently reproduce prefix',report['direct_shells']==report['prefix'][:13])
    check('atomic endpoint strict and weak counts',
          [(x['strict_count'],x['weak_count']) for x in report['endpoint_checks']]
          ==[(0,1),(1,1),(1,2),(6,7),(7,8),(12,13),(7,7),(76,76)])
    check('zero atom equality exact', c.compare((),())==0)
    check('radical equality ignores order',c.compare((2,3,2),(3,2,2))==0)
    check('opposite comparisons exact',c.compare((2,),(3,))==-1 and c.compare((3,),(2,))==1)
    check('root integer exact', c.root_bounds(9)==(3*(1<<96),3*(1<<96)))
    for d in [2,3,5,7,10,1294]:
        a,b=c.root_bounds(d)
        check('root enclosure '+str(d),a*a<d*(1<<192)<b*b)
    check('squarefree independent trial division',all(c.squarefree(n) for n in [1,2,3,6,10,30])
          and not any(c.squarefree(n) for n in [4,8,9,12,18,25]))
    check('minimal exact bound works',c.exact(0,0)['prefix']==[1])
    # Integer-weight relaxation certifies an upper bound on every admitted C++
    # prefix without running the 428-million-vector n35 enumeration.
    dp=[0]*36
    dp[0]=1
    for d in range(2,36*36):
        if c.squarefree(d):
            weight=math.isqrt(d)
            for total in range(weight,36):
                dp[total]+=dp[total-weight]
    check('independent relaxed n35 count bound',sum(dp)==2878677965)
    check('C++ uint64 count capacity proved',sum(dp)<2**64)
    rejected('coarse enumeration ambiguity abort',lambda:c.enumerate_sums(7,bits=1))
    rejected('coarse endpoint ambiguity abort',lambda:c.compare((2,),(3,),bits=1))
    for value in [None,True,False,1.5,'20',-1,21]:
        rejected('invalid exact bound '+repr(value),lambda value=value:c.exact(value,0))
    for value in [None,True,False,1.0,'96',0,-1,257]:
        rejected('invalid precision '+repr(value),lambda value=value:c.root_bounds(2,value))
    for value in [None,True,0,-1,1.25,'2',10**9+1]:
        rejected('invalid radicand '+repr(value),lambda value=value:c.root_bounds(value))
    for endpoint in [(4,),[0],[True],['2'],'2',{2:1}]:
        rejected('invalid canonical endpoint '+repr(endpoint),lambda endpoint=endpoint:c.compare(endpoint,()))
    rejected('record bound',lambda:c.enumerate_sums(8,record=True))
    rejected('invalid boolean include unit',lambda:c.enumerate_sums(2,include_unit=1))
    rejected('invalid shell bound',lambda:c.exact(10,12))
    rejected('full C++ requires opt in',lambda:c.cpp(35))
    rejected('invalid C++ bool permission',lambda:c.cpp(0,1))
    for ns in [(),[True],[0],[10001],['1'],1]:
        rejected('invalid diagnostic input '+repr(ns),lambda ns=ns:c.diagnostics(ns))
    with tempfile.TemporaryDirectory(prefix='report172-tests-') as temporary:
        temp=Path(temporary)
        for name in ['oeis_35_historical.json','SHA256.json']:
            shutil.copyfile(c.ROOT/'fixtures'/name,temp/name)
        data=json.loads((temp/'oeis_35_historical.json').read_text())
        data['terms']['35']+=1
        (temp/'oeis_35_historical.json').write_bytes(c.json_bytes(data))
        rejected('mutated fixture rejected',lambda:c.load_fixture(temp))
        shutil.copyfile(c.ROOT/'fixtures/oeis_35_historical.json',temp/'oeis_35_historical.json')
        (temp/'SHA256.json').write_text('{}\n')
        rejected('mutated checksum manifest rejected',lambda:c.load_fixture(temp))
        target=temp/'exclusive.json'
        c.write_new(target,b'original')
        rejected('exclusive output no clobber',lambda:c.write_new(target,b'replacement'))
        check('exclusive output unchanged',target.read_bytes()==b'original')
        link=temp/'link.json'
        link.symlink_to(target)
        rejected('symlink output rejected',lambda:c.write_new(link,b'replacement'))
        check('symlink target unchanged',target.read_bytes()==b'original')
        link.unlink()
        link.symlink_to(temp/'missing')
        rejected('broken symlink output rejected',lambda:c.write_new(link,b'replacement'))
        rejected('JSON nonfinite values rejected',lambda:c.json_bytes({'x':math.inf}))
        rejected('write_new type rejected',lambda:c.write_new(temp/'bad', 'text'))
        binary=temp/'enumerate_roots'
        result=subprocess.run(['g++','-O3','-std=c++17',str(c.ROOT/'code/enumerate_roots.cpp'),'-o',str(binary)],capture_output=True,text=True)
        check('C++ compilation succeeds',result.returncode==0)
        result=subprocess.run([str(binary),'20','48'],capture_output=True,text=True)
        check('independent C++ exact n20 succeeds',result.returncode==0)
        cpp=json.loads(result.stdout)
        check('independent C++ agrees with Python all terms',cpp['prefix']==report['prefix'] and cpp['vectors']==458000)
        for arguments in [[],['-1'],['36'],['true'],['20;touch','x'],['0','0'],['0','49'],['0','1','x'],['9999999999999999999999999']]:
            result=subprocess.run([str(binary)]+arguments,capture_output=True,text=True)
            check('C++ rejects malformed arguments '+repr(arguments),result.returncode!=0 and not result.stdout)
        result=subprocess.run([str(binary),'6','1'],capture_output=True,text=True)
        check('C++ ambiguity abort without partial JSON',result.returncode!=0 and 'ambiguous' in result.stderr and not result.stdout)
        result=subprocess.run([sys.executable,str(c.ROOT/'code/companion.py'),'exact','--n','-1'],capture_output=True,text=True)
        check('CLI rejects invalid bound',result.returncode!=0 and not result.stdout)
        result=subprocess.run([sys.executable,str(c.ROOT/'code/companion.py'),'exact','--output',str(target)],capture_output=True,text=True)
        check('CLI rejects existing output before work',result.returncode!=0 and target.read_bytes()==b'original')
    numerical=c.diagnostics([5])
    check('numerical output distinctly noncertified',numerical['status']=='EXPLORATORY_NONCERTIFIED')
    check('positive log-product tail estimate',numerical['results'][0]['positive_analytic_F_tail_bound_evaluated_in_binary64']>0)
    check('no formal correction represented as theorem','correction' not in json.dumps(numerical))
    return {'status':'PASS','python_optimized':not __debug__,'checks_passed':len(passed),
            'checks':passed,'fresh_coverage':{'cumulative_max_n':20,'cumulative_vectors':458000,
            'direct_shell_max_n':12,'direct_shell_vectors':14155,'cpp_max_n':20},
            'historical_n35_rerun':False,'critical_validation':'Explicit exceptions, not assert statements'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        if args.output:
            c.require(not args.output.exists() and not args.output.is_symlink(),'refusing existing output')
        result=run_tests()
        if args.output:
            c.write_new(args.output,c.json_bytes(result))
        else:
            print(c.json_bytes(result).decode(),end='')
    except (ValueError,OSError,subprocess.SubprocessError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2
    return 0
if __name__=='__main__':
    raise SystemExit(main())
