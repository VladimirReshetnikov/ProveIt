#!/usr/bin/env python3
"""Adversarial proof-input controls, separate from finite machine evidence.

These are tests of the source/certificate audit boundaries. They are not a
replacement for the exhaustive symbolic runtime or a proof of <=218 states.
"""
from pathlib import Path
import argparse,copy,importlib.util,json,shutil,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'portable'))
import check_source as source
import check_runtime as runtime
from construct import dump

def main():
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--vendor',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--certificates',type=Path,default=ROOT/'certificates');a=ap.parse_args()
    old=json.loads((a.baseline/'machine/sites219.json').read_text());results=[]
    def rejects(name,call):
        try:call()
        except (AssertionError,ValueError,KeyError,IndexError)as e:
            results.append(dict(name=name,status='REJECTED',exception=type(e).__name__))
        else:raise AssertionError('Negative control was accepted: '+name)
    sites=json.loads((ROOT/'machine/retagged/sites.json').read_text());bad=copy.deepcopy(sites);bad[118][2]=2
    rejects('missing_one_required_continuation_retag',lambda:source.prove(old,bad,'retagged'))
    zero=json.loads((ROOT/'machine/zero_terminal/sites.json').read_text());badzero=copy.deepcopy(zero);badzero[4570][1:]=['CB',1]
    rejects('missing_one_zero_terminal_substitution',lambda:source.prove(old,badzero,'zero_terminal'))
    badguard=copy.deepcopy(zero);badguard[4568][2]=5
    rejects('changed_zero_guard_predecessor',lambda:source.prove(old,badguard,'zero_terminal'))
    badsyntax=copy.deepcopy(sites);badsyntax[10][0]=badsyntax[9][0]
    rejects('duplicate_leaf_address',lambda:source.prove(old,badsyntax,'retagged'))
    name='retagged';spec=runtime.SPECS[name]
    table=runtime.read_table(ROOT/'machine'/name/'k219.native.tm')
    reference=a.certificates/name
    with tempfile.TemporaryDirectory(prefix='k219-negative-')as temporary:
        out=Path(temporary)
        def reset():
            for filename in ('runtime.json','cases.json','startup.json','canonical.tm'):
                shutil.copy2(reference/filename,out/filename)
        def changed_case(label,edit):
            reset();p=out/'cases.json';cases=json.loads(p.read_text());edit(cases);dump(p,cases)
            rejects(label,lambda:runtime.audit(table,sites,spec,out,a.vendor))
        changed_case('omitted_generic_case',lambda x:x.pop())
        changed_case('duplicated_generic_case',lambda x:x.__setitem__(1,copy.deepcopy(x[0])))
        changed_case('nonpositive_duration_constant',lambda x:x[0]['duration'].__setitem__(0,0))
        reset();p=out/'runtime.json';rec=json.loads(p.read_text());rec['block_schemas'][0]['trace'][0][1][2]^=1;dump(p,rec)
        rejects('false_exact_table_block_lemma',lambda:runtime.audit(table,sites,spec,out,a.vendor))
        reset();p=out/'runtime.json';rec=json.loads(p.read_text());rec['directly_used_rows'].pop();dump(p,rec)
        rejects('omitted_physical_row_coverage',lambda:runtime.audit(table,sites,spec,out,a.vendor))
        reset();p=out/'startup.json';rec=json.loads(p.read_text());rec['startup']['steps']+=1;dump(p,rec)
        rejects('wrong_blank_startup_duration',lambda:runtime.audit(table,sites,spec,out,a.vendor))
    dump(a.output,dict(status='ALL_NEGATIVE_CONTROLS_REJECTED',controls=results,count=len(results),scope='Malformed source and certificate rejection tests only; independent of the mathematical completeness claim.'))
    print('ALL_NEGATIVE_CONTROLS_REJECTED',len(results))
if __name__=='__main__':main()
