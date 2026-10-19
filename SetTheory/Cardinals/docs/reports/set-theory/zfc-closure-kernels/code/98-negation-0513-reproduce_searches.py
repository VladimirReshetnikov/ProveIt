#!/usr/bin/env python3
"""Reproduce the bounded runtime searches, with pinned explicit inputs.

The complete run takes several minutes. It uses Python's standard library and
a C++17 compiler, writes only the chosen output directory and temporary files,
and performs no network operation. All work remains a bounded search.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,subprocess,sys,tempfile

TABLE_SHA='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
CASES_SHA='71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--table',required=True,type=Path)
    p.add_argument('--instruction-cases',required=True,type=Path,help='Literal fixture, plain text or .gz')
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--compiler',default='g++')
    a=p.parse_args();here=Path(__file__).resolve().parent;out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    data=a.table.read_bytes();assert hashlib.sha256(data).hexdigest()==TABLE_SHA
    case_data=a.instruction_cases.read_bytes()
    if a.instruction_cases.suffix=='.gz':case_data=gzip.decompress(case_data)
    assert hashlib.sha256(case_data).hexdigest()==CASES_SHA
    runs=[];env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    def run(name,argv):
        print(name,flush=True)
        with (out/(name+'.stdout')).open('w') as stdout,(out/(name+'.stderr')).open('w') as stderr:
            completed=subprocess.run(argv,cwd=out,env=env,stdout=stdout,stderr=stderr)
        runs.append(dict(name=name,argv=list(map(str,argv)),returncode=completed.returncode))
        (out/'reproduction-commands.json').write_text(json.dumps(runs,indent=2)+'\n')
        if completed.returncode:raise SystemExit(f'{name} failed; see recorded stdout/stderr')
    with tempfile.TemporaryDirectory(prefix='zfc-runtime-reproduction-') as td:
        temp=Path(td);fixture=temp/'instruction-cases.txt';fixture.write_bytes(case_data)
        binaries={}
        for stem in ('shared_row_superopt','coupled_tail_superopt','lazy_core_superopt'):
            binaries[stem]=temp/stem;run('compile-'+stem,[a.compiler,'-O3','-std=c++17',str(here/(stem+'.cpp')),'-o',str(binaries[stem])])
        for name,value in (('append1',1),('append0',0),('noappend',-1)):
            run('fixtures-'+name,[sys.executable,'-B',str(here/'make_macro_cases.py'),str(a.table.resolve()),str(out/('macro-cases-'+name+'.txt')),'--append',str(value)])
        run('shared-row',[str(binaries['shared_row_superopt']),str(fixture)])
        run('coupled-tail',[str(binaries['coupled_tail_superopt']),str(out/'macro-cases-append1.txt')])
        run('coupled-tail-alltargets',[str(binaries['coupled_tail_superopt']),str(out/'macro-cases-append1.txt'),'coupled-tail-alltargets'])
        for row_count in (5,7):
            for name in ('append1','append0','noappend'):
                prefix=f'lazy-core{row_count}-{name}'
                run(prefix,[str(binaries['lazy_core_superopt']),str(out/('macro-cases-'+name+'.txt')),prefix,'600',str(row_count)])
                result=json.loads((out/(prefix+'-summary.json')).read_text())
                assert result['completed'],f'{prefix} hit its explicit time cap'
    print('Completed all finite searches; consult their recorded scope and clocks.')

if __name__=='__main__':main()
