#!/usr/bin/env python3
"""Bounded rejection and output-safety checks, active with and without -O."""
from __future__ import annotations
import argparse
import ast
from pathlib import Path
import subprocess
import sys
import tempfile
from common import (ROOT, REPORT_NUMBER, child_environment, emit, integer_receipt,
                    new_file_path, python_command, require)
from exact_counts import (ascent_count, checked_word, fast_avoidance, is_ascent,
                          literal_avoidance, raw_ascent_words, recurrence_count,
                          triple_class_prefix, verify as verify_counts)
from upper_bound import (decode_word, encode_word, finite_upper_bound, skeleton_bound,
                         table_term, vandermonde_bound, verify as verify_upper)
from positive_rows import (all_length_parameters, bounded_row, doubled_seed,
                           empty_distribution, group_cells, pad_records, positive_word,
                           ranks_to_stars, recover_rows, repair, repair_budget,
                           rows_checked, stars_to_ranks, undo_doubled_seed,
                           weak_compositions, verify_exhaustive)


def verify():
    passed = []
    def reject(label,call):
        try:
            call()
        except (ValueError,RuntimeError,OSError,ArithmeticError):
            passed.append(label)
            return
        raise RuntimeError('guard failed: '+label)
    bad_scalar = (True,1.0,'1',None)
    for label,fun,lo,hi in (
            ('raw words',raw_ascent_words,0,9),('literal common',triple_class_prefix,0,11),
            ('count verifier',verify_counts,0,9),('upper verifier',verify_upper,0,9),
            ('finite upper',finite_upper_bound,0,64),('array verifier',verify_exhaustive,2,9),
            ('all-length target',all_length_parameters,100,10_000)):
        for value in (lo-1,hi+1)+bad_scalar:
            reject(label+' scalar '+repr(value),lambda f=fun,v=value:f(v))
    for pattern in (99,101,111,True,100.0,'100',None):
        for fun,argument in ((encode_word,()),(decode_word,(0,(),(),(),())),(recurrence_count,0)):
            reject(fun.__name__+' pattern '+repr(pattern),lambda f=fun,a=argument,p=pattern:f(a,p))
    for value in (-1,16)+bad_scalar:
        reject('recurrence n '+repr(value),lambda v=value:recurrence_count(v,100))
    for fun in (checked_word,ascent_count,is_ascent,literal_avoidance,fast_avoidance):
        for value in (None,'012',True,[True],[1.0],[-1],[100001]):
            reject(fun.__name__+' malformed word '+repr(value),lambda f=fun,v=value:f(v))
    reject('literal cubic-work cap',lambda:literal_avoidance([0]*81))
    reject('raw word cap',lambda:checked_word([0]*100001))
    reject('encoding length cap',lambda:encode_word([0]*65,100))
    reject('illegal ascent entry',lambda:encode_word((0,2),100))
    reject('100 forbidden subsequence',lambda:encode_word((0,1,0,0),100))
    reject('110 forbidden subsequence',lambda:encode_word((0,1,1,0),110))
    malformed = (None,[],(),(True,(),(),(),()),(65,(),(),(),()),
        (1,[],(),(1,),((0,),)),(1,(True,),(0,),(1,),((),)),
        (3,(1,0),(0,0),(3,),((0,),)),(2,(1,),(True,),(2,),((0,),)),
        (1,(),(),(True,),((0,),)),(2,(),(),(1,),((0,),)),
        (1,(),(),(1,),(0,)),(2,(),(),(2,),((0,0),)),
        (1,(),(),(1,),((True,),)),(1,(),(),(1,),((1,),)),
        (1,(0,),(0,),(1,),((),)),(2,(),(),(1,1),((0,),(1,))))
    for i,value in enumerate(malformed):
        reject('malformed encoding %d'%i,lambda v=value:decode_word(v,100))
    reject('first occurrence status',lambda:decode_word((2,(0,),(0,),(1,1),((),(0,))),110))
    reject('last occurrence status',lambda:decode_word((2,(1,),(0,),(1,1),((0,),())),100))
    for r in (-1,64)+bad_scalar:
        reject('Vandermonde r '+repr(r),lambda v=r:vandermonde_bound(v,(1,),(1,)))
    for value in (None,'1',True,[True],[1.0],[-1],[65],[1]*65):
        reject('Vandermonde runs '+repr(value),lambda v=value:vandermonde_bound(0,v,()))
    for value in (None,'1',True,[True],[1.0],[-1],[2],[]):
        reject('Vandermonde retained '+repr(value),lambda v=value:vandermonde_bound(0,(1,),v))
    reject('Vandermonde total cap',lambda:vandermonde_bound(1,(64,1),(64,0)))
    reject('Vandermonde retained total',lambda:vandermonde_bound(1,(2,),(2,)))
    reject('Vandermonde run count',lambda:vandermonde_bound(0,(1,1),(1,1)))
    for value in (0,10001)+bad_scalar:
        reject('table size '+repr(value),lambda v=value:table_term(v,1))
    for value in (0,3)+bad_scalar:
        reject('table dimension '+repr(value),lambda v=value:table_term(2,v))
    reject('skeleton invalid n',lambda:skeleton_bound(0,0))
    reject('skeleton invalid r',lambda:skeleton_bound(1,1))
    for fun in (bounded_row,stars_to_ranks):
        for value in (None,'1',[],[True],[1.0],[-1],[10001],[0]*401,[6000,6000]):
            reject(fun.__name__+' row '+repr(value)[:60],lambda f=fun,v=value:f(v))
    for fun in (rows_checked,repair,positive_word):
        for value in (None,'1',[],[(0,0)],[(1,),(1,)],[(True,)],[(10001,)]):
            reject(fun.__name__+' array '+repr(value),lambda f=fun,v=value:f(v))
    reject('positive-row zero total',lambda:positive_word(((0,),)))
    for width in (0,401)+bad_scalar:
        reject('rank inverse width '+repr(width),lambda v=width:ranks_to_stars((),v))
    for ranks in (None,'1',[True],[-1],[1],[0,0],[1,0],[0]*10001):
        reject('rank inverse subset '+repr(ranks)[:60],lambda v=ranks:ranks_to_stars(v,1))
    for total in (-1,9)+bad_scalar:
        reject('composition total '+repr(total),lambda v=total:weak_compositions(v,1))
    for cells in (0,37)+bad_scalar:
        reject('composition cells '+repr(cells),lambda v=cells:weak_compositions(1,v))
    reject('enumeration work budget',lambda:weak_compositions(8,36))
    reject('triangular grouping size',lambda:group_cells((1,2),2))
    reject('triangular grouping bad cell',lambda:group_cells((True,),1))
    reject('row decoder empty lengths',lambda:recover_rows((0,),()))
    reject('row decoder incorrect seed',lambda:recover_rows((0,0,1,2),(1,1)))
    reject('row decoder incorrect length',lambda:recover_rows((0,0),(2,)))
    reject('row decoder repeated block',lambda:recover_rows((0,0,0),(2,)))
    for r in (0,401)+bad_scalar:
        reject('doubling seed '+repr(r),lambda v=r:doubled_seed((0,0),v))
        reject('undoubling seed '+repr(r),lambda v=r:undo_doubled_seed((0,0,1),v))
    reject('doubling incorrect seed',lambda:doubled_seed((0,0,1),2))
    reject('doubling repeated suffix',lambda:doubled_seed((0,0,0),1))
    reject('doubling first suffix condition',lambda:doubled_seed((0,1),1))
    reject('undoubling incorrect seed',lambda:undo_doubled_seed((0,1,1),1))
    reject('undoubling suffix below seed',lambda:undo_doubled_seed((0,0,0),1))
    for N in (-1,20001)+bad_scalar:
        reject('padding target '+repr(N),lambda v=N:pad_records((0,),v))
    reject('padding cannot shorten',lambda:pad_records((0,1),1))
    reject('padding requires legal input',lambda:pad_records((0,2),3))
    for value in (0,10001)+bad_scalar:
        reject('repair budget r '+repr(value),lambda v=value:repair_budget(v,1))
        reject('repair budget q '+repr(value),lambda v=value:repair_budget(1,v))
    for value in (0,17)+bad_scalar:
        reject('DP r '+repr(value),lambda v=value:empty_distribution(v,1))
    for value in (0,129)+bad_scalar:
        reject('DP q '+repr(value),lambda v=value:empty_distribution(1,v))
    reject('all-length class selector',lambda:all_length_parameters(100,1))
    for value in (-1,True,1.0,'1',None):
        reject('integer receipt '+repr(value),lambda v=value:integer_receipt(v))
    reject('integer receipt bit budget',lambda:integer_receipt(1<<2_000_000))
    require('exact_decimal' not in integer_receipt(10**1000),'huge count converted to decimal')
    passed.append('huge counts are hashed as bytes without decimal conversion')
    require(is_ascent(()) and literal_avoidance(())==(True,True,True),'empty convention')
    require(not is_ascent((0,0,2)) and is_ascent((0,1,2)),'entering-edge convention')
    require(not fast_avoidance((2,0,1,0))[1],'100 must be a subsequence')
    require(not fast_avoidance((2,1,2,0))[2],'110 must be a subsequence')
    require(pad_records((),3)==(0,1,2),'empty padding boundary')
    for p in (100,110):
        for word in ((),(0,),(0,0,0)):
            require(decode_word(encode_word(word,p),p)==word,'encoding boundary round trip')
    require(stars_to_ranks((0,))==() and ranks_to_stars((),1)==(0,),'empty row boundary')
    require(repair(((0,),))==((1,),),'single empty row repair')
    require(positive_word(((1,),))==((0,0),(1,)),'r=1 construction boundary')
    require(doubled_seed((0,0),1)==(0,0,1),'r=1 doubling boundary')
    passed.append('empty, strict-ascent, arbitrary-subsequence and r=1 boundaries pass')
    import exact_counts
    old_states,old_transitions = exact_counts.MAX_STATES,exact_counts.MAX_TRANSITIONS
    try:
        exact_counts.MAX_STATES = 0
        reject('recurrence state budget',lambda:recurrence_count(2,100))
        exact_counts.MAX_STATES = old_states
        exact_counts.MAX_TRANSITIONS = 0
        reject('recurrence transition budget',lambda:recurrence_count(2,110))
    finally:
        exact_counts.MAX_STATES,exact_counts.MAX_TRANSITIONS = old_states,old_transitions
    require(sys.get_int_max_str_digits()==640,'decimal cap must be 640')
    require(sys.dont_write_bytecode,'bytecode must be disabled')
    reject('decimal input exceeds 640 digits',lambda:int('1'*641))
    reject('decimal output exceeds 640 digits',lambda:str(10**641))
    for source in sorted((ROOT/'code').glob('*.py')):
        require(source.stat().st_size <= 512_000,'source exceeds inspection cap')
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source.read_text()))),
                'validation must not depend on assert: '+source.name)
    passed.append('all public Python sources contain no assert statements')
    for level in (-1,3,True,1.0,'1'):
        reject('optimization level '+repr(level),lambda v=level:python_command(v))
    hostile = child_environment()
    hostile.update(PYTHONDONTWRITEBYTECODE='0',PYTHONINTMAXSTRDIGITS='0',PYTHONOPTIMIZE='2')
    for level in (0,1,2):
        probe = ('import sys;sys.exit(0 if sys.get_int_max_str_digits()==640 '
                 'and sys.dont_write_bytecode and sys.flags.optimize==%d else 2)'%level)
        result = subprocess.run(python_command(level)+['-E','-c',probe],env=hostile,
                                capture_output=True,check=False,timeout=30)
        require(result.returncode==0,'explicit child interpreter flags lost')
        passed.append('explicit -B/-X cap640 at optimization level %d under hostile environment'%level)
    with tempfile.TemporaryDirectory(prefix='report243-guards-',dir='/tmp') as temp:
        work = Path(temp)
        existing = work/'existing'; existing.write_text('unchanged',encoding='utf-8')
        directory = work/'directory'; directory.mkdir()
        live = work/'live'; live.symlink_to(directory,target_is_directory=True)
        dead = work/'dead'; dead.symlink_to(work/'absent',target_is_directory=True)
        invalid = ['',str(existing),str(directory),str(ROOT/'forbidden.json'),
                   str(live/'out'),str(dead/'out'),str(work)+'/directory/../out',
                   str(work)+'/./out',str(work/'absent/out'),str(work/'back\\slash')]
        for i,path in enumerate(invalid):
            reject('output path case %d'%i,lambda p=path:new_file_path(p))
        for value in (True,1,None,b'bytes'):
            reject('output path type '+repr(value),lambda v=value:new_file_path(v))
        destination = work/'valid.json'
        emit({'ok':True},str(destination))
        reject('exclusive file cannot replace',lambda:emit({'ok':False},str(destination)))
        require(existing.read_text()=='unchanged','existing file was modified')
        commands = [('exact_counts.py',['--raw-n','10']),('exact_counts.py',['--raw-n','1'*641]),
                    ('upper_bound.py',['--max-n','10']),('positive_rows.py',['--max-n','10']),
                    ('positive_rows.py',['--output',str(existing)]),
                    ('positive_rows.py',['--output',str(live/'bad')]),
                    ('exact_counts.py',['--output',str(existing)]),
                    ('upper_bound.py',['--unknown'])]
        for i,(script,args) in enumerate(commands):
            result = subprocess.run(python_command()+[str(ROOT/'code'/script)]+args,
                                    env=child_environment(),capture_output=True,check=False,timeout=30)
            require(result.returncode!=0,'CLI accepted invalid arguments')
            passed.append('CLI rejection %d'%i)
    return {'status':'PASS','report_number':REPORT_NUMBER,'checks_passed':len(passed),
            'checks':passed,'scope':'Finite input, budget, interpreter and output-path guards; not a hostile-concurrency sandbox.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(),args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
