#!/usr/bin/env python3
"""Run exact positive checks and deliberately corrupt JSON in normal Python and -O."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent


def require(condition,message):
    if not condition:raise RuntimeError(message)


def run(flags,arguments):
    return subprocess.run([sys.executable,'-I','-B',*flags,str(ROOT/'verify.py'),*arguments],
                          cwd=ROOT,text=True,capture_output=True,check=False,timeout=180)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extended',action='store_true',help='all checks always run')
    parser.parse_args()
    positive=[]
    for flags in ([],['-O']):
        passed=run(flags,[])
        require(passed.returncode==0,'positive run failed: '+passed.stderr)
        result=json.loads(passed.stdout)
        require(result.get('status')=='PASS' and result.get('all_checks_passed') is True,'missing PASS marker')
        require(result.get('parameter_tests',{}).get('warm_cache_type_rejections')==54,'warm-cache guards did not all run')
        positive.append(passed.stdout)
    require(positive[0]==positive[1],'normal and optimized outputs differ')
    original=json.loads((ROOT/'data/certificates.json').read_text(encoding='utf-8'))
    mutants=[]
    def add(label,edit):
        item=copy.deepcopy(original);edit(item);mutants.append((label,json.dumps(item)))
    add('inverse quadratic coefficient',lambda d:d['inverse_refinement'].__setitem__('gprime_g_coefficient_of_D_inverse_squared','0'))
    add('inverse cubic coefficient',lambda d:d['inverse_refinement'].__setitem__('minus_half_Hsecond_g_squared_coefficient_of_D_inverse_cubed','3/8'))
    add('inverse derivative coefficient',lambda d:d['inverse_refinement'].__setitem__('lambda_prime_coefficient_of_lambda_inverse','1/2'))
    add('boundary lower ceiling',lambda d:d['finite_threshold_boundaries']['cases'][0].__setitem__('ceil_x_minus_epsilon',0))
    add('boundary upper ceiling',lambda d:d['finite_threshold_boundaries']['cases'][0].__setitem__('ceil_x_plus_epsilon',0))
    add('boundary floor',lambda d:d['finite_threshold_boundaries']['cases'][0].__setitem__('floor_x_minus_epsilon',99))
    add('boundary strict margin',lambda d:d['finite_threshold_boundaries']['cases'][0].__setitem__('strict_lower_margin','0'))
    add('boundary case missing',lambda d:d['finite_threshold_boundaries']['cases'].pop())
    add('boundary equality coverage',lambda d:d['finite_threshold_boundaries'].__setitem__('exact_upper_equality_cases',0))
    add('finite boundary scope',lambda d:d['finite_threshold_boundaries'].__setitem__('scope','Effective asymptotic proof'))
    add('gamma coefficient',lambda d:d['d_polynomials'][1].__setitem__(1,'1/5'))
    add('Poisson coefficient',lambda d:d['q_polynomials'][4].__setitem__(2,'0'))
    add('fifth Poisson coefficient',lambda d:d['q_polynomials'][5].__setitem__(1,'0'))
    add('q value',lambda d:d['q_at_one'].__setitem__(1,'13/97'))
    add('carrier',lambda d:d['elementary_carrier'].__setitem__(2,'-119/18433'))
    add('log carrier',lambda d:d['log_elementary_carrier'].__setitem__(3,'0'))
    add('inserted shift',lambda d:d['shifted_q_polynomials']['1'][1].__setitem__(1,'0'))
    add('factorial quotient',lambda d:d['factorial_moment_quotients']['2'].__setitem__(3,'0'))
    add('mean',lambda d:d['mean_h_powers'].__setitem__('2','0'))
    add('variance',lambda d:d['variance_h_powers'].__setitem__('2','0'))
    add('fixed log',lambda d:d['fixed_shift_log_y'].__setitem__(1,'1/8'))
    add('fixed ratio',lambda d:d['fixed_shift_R_y'].__setitem__(2,'1/8'))
    add('even rare probability',lambda d:d['rare_even_relative_h'].__setitem__(4,'0'))
    add('odd rare probability',lambda d:d['rare_odd_relative_h'].__setitem__(4,'0'))
    add('empty count',lambda d:d['counts_n0_to100'].__setitem__(0,0))
    add('last count',lambda d:d['counts_n0_to100'].__setitem__(100,d['counts_n0_to100'][100]+1))
    add('recursive histogram',lambda d:d['recursive_histograms_n0_to8']['8'].__setitem__('0',1))
    add('source displayed value',lambda d:d['source']['displayed_values'].__setitem__(0,4))
    add('source offset',lambda d:d['source'].__setitem__('displayed_offset',0))
    add('source URL',lambda d:d['source'].__setitem__('url','https://example.invalid/'))
    add('trailing zero',lambda d:d['q_polynomials'][1].append('0'))
    add('noncanonical fraction',lambda d:d['q_at_one'].__setitem__(1,'26/192'))
    add('fraction JSON number',lambda d:d['q_at_one'].__setitem__(0,1))
    add('Boolean count',lambda d:d['counts_n0_to100'].__setitem__(0,True))
    add('floating count',lambda d:d['counts_n0_to100'].__setitem__(0,1.0))
    add('Boolean schema',lambda d:d.__setitem__('schema_version',True))
    add('missing field',lambda d:d.pop('mean_h_powers'))
    add('extra field',lambda d:d.__setitem__('unexpected',0))
    add('short certificate',lambda d:d['counts_n0_to100'].pop())
    add('uncertified scope changed',lambda d:d['scope'].__setitem__('numerical_remainder_bounds_certified',True))
    mutants.append(('duplicate JSON key','{"report":176,'+json.dumps(original)[1:]))
    mutants.append(('nonfinite JSON','{"report":NaN,'+json.dumps(original)[1:]))
    mutants.append(('invalid JSON','{'))
    mutants.append(('wrong top-level type','[]'))
    reference=json.loads((ROOT/'references/independent_results.json').read_text(encoding='utf-8'))
    bad_references=[]
    for label,value in [('reference coefficient','0'),('reference boolean',True),('reference executable syntax',"__import__('os')"),('reference giant degree','(v**20)**20'),('reference giant constant','(999**20)**20')]:
        item=copy.deepcopy(reference);item['q_j'][5]=value
        bad_references.append((label,json.dumps(item)))
    manuscript=(ROOT/'report.tex').read_text(encoding='utf-8')
    marker=r'The first values for $n=0,\ldots,8$ are'
    bad_manuscripts=[
        ('old wrong n6',manuscript.replace('7950960','7944960',1)),
        ('short initial prefix',manuscript.replace(r',\ 30400755840','',1)),
        ('long initial prefix',manuscript.replace('30400755840.','30400755840, 1.',1)),
        ('arithmetic initial value',manuscript.replace('7950960','7950960+0',1)),
        ('decimal initial value',manuscript.replace('7950960','7950960.0',1)),
        ('negative initial value',manuscript.replace('7950960','-7950960',1)),
        ('TeX command initial value',manuscript.replace('7950960',r'\num{7950960}',1)),
        ('missing initial marker',manuscript.replace(marker,'Initial values:',1)),
        ('duplicate initial marker',manuscript+'\n'+marker),
        ('missing initial display terminator',manuscript.replace('30400755840.\n\\]','30400755840.\n',1)),
    ]
    require(all(content!=manuscript for _,content in bad_manuscripts),'a manuscript mutation did not change its target')
    rejected=0
    with tempfile.TemporaryDirectory(prefix='report176-corruption-') as directory:
        path=Path(directory)/'invalid.json'
        for label,content in mutants:
            path.write_text(content,encoding='utf-8')
            for flags in ([],['-O']):
                failure=run(flags,['--data',str(path)])
                require(failure.returncode==1 and 'VERIFICATION FAILED:' in failure.stderr,
                        label+' not rejected in mode '+str(flags)+': '+failure.stdout+failure.stderr)
                rejected+=1
        for label,content in bad_references:
            path.write_text(content,encoding='utf-8')
            for flags in ([],['-O']):
                failure=run(flags,['--reference',str(path)])
                require(failure.returncode==1 and 'VERIFICATION FAILED:' in failure.stderr,label+' not rejected: '+failure.stdout+failure.stderr)
                rejected+=1
        for label,content in bad_manuscripts:
            path.write_text(content,encoding='utf-8')
            for flags in ([],['-O']):
                failure=run(flags,['--manuscript',str(path)])
                require(failure.returncode==1 and 'VERIFICATION FAILED:' in failure.stderr,label+' not rejected: '+failure.stdout+failure.stderr)
                rejected+=1
        path.unlink()
        for flags in ([],['-O']):
            failure=run(flags,['--data',str(path)])
            require(failure.returncode==1 and 'VERIFICATION FAILED:' in failure.stderr,'missing certificate accepted')
            rejected+=1
    print(json.dumps({'status':'PASS','all_guard_tests_passed':True,'report':176,
                      'positive_runs':['normal','optimized (-O)'],'identical_positive_output':True,
                      'corrupt_certificates_per_mode':len(mutants),'corrupt_manuscripts_per_mode':len(bad_manuscripts),'corrupt_references_per_mode':len(bad_references),'missing_input_rejections':2,
                      'total_negative_rejections':rejected,'parameter_checks_run_in_both_modes':True,'warm_cache_type_rejections_per_verifier':54},sort_keys=True,indent=2))

if __name__=='__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,KeyError,TypeError,subprocess.TimeoutExpired) as exc:
        print('GUARD TEST FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
