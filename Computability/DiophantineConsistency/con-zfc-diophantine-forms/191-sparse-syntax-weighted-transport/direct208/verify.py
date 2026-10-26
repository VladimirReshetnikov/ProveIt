#!/usr/bin/env python3
"""Run independent checks, validate printed rows, and replay a fresh rebuild."""
from pathlib import Path
import argparse,contextlib,hashlib,io,json,re,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
import check_local,check_chain
def require(ok,msg):
    if not ok:raise ValueError(msg)
def capture(fn):
    s=io.StringIO()
    with contextlib.redirect_stdout(s):fn()
    return json.loads(s.getvalue())
def parse_printed(text,expected):
    pattern=re.compile(r'% RBEGIN (\d+)\n(.*?)% REND \1\n',re.S)
    matches=list(pattern.finditer(text))
    require(len(matches)==148,'printed row count')
    for i,match in enumerate(matches):
        require(int(match.group(1))==i,'printed row order')
        body=match.group(2).replace('R_{'+str(i)+'}={}&','')
        body=re.sub(r'\\\\\*?(?:\[3pt\])?','',body).replace('&','').replace('\n','').strip()
        terms={}
        for fragment in re.findall(r'[+-]?[^+-]+',body):
            sign=-1 if fragment.startswith('-') else 1
            fragment=fragment.lstrip('+-');mon=[]
            for v,k in re.findall(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',fragment):
                require(int(v)<208,'printed index range');mon += [int(v)]*(int(k) if k else 1)
            number=re.sub(r'x_\{\d+\}(?:\^\{\d+\})?','',fragment)
            require(number=='' or number.isdigit(),'unrecognized printed coefficient')
            coef=sign*(int(number) if number else 1);key=tuple(sorted(mon))
            terms[key]=terms.get(key,0)+coef
        require(terms=={tuple(m):c for c,m in expected[i]['terms']},'printed coefficient mismatch in R'+str(i))
    return len(matches)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--skip-rebuild',action='store_true')
    args=ap.parse_args()
    ledger=json.loads((ROOT/'SOURCES.json').read_text())
    for name,sha in ledger['source_files'].items():require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==sha,'frozen source changed: '+name)
    local=capture(check_local.main);chain=capture(check_chain.main)
    endpoint=ROOT/'equations/principal208';e=json.loads((endpoint/'equation.json').read_text())
    require(e['domain']=='unrestricted integers','endpoint domain')
    printed=(endpoint/'residuals.tex').read_text();n=parse_printed(printed,e['residuals'])
    broken=printed.replace('x_{','x_{999',1);bad=False
    try:parse_printed(broken,e['residuals'])
    except ValueError:bad=True
    require(bad,'printed mutation accepted')
    count=0
    if not args.skip_rebuild:
        with tempfile.TemporaryDirectory(prefix='direct208-rebuild-') as tmp:
            dest=Path(tmp);command=[sys.executable]
            if sys.flags.optimize:command.append('-O')
            command += ['-B',str(ROOT/'build.py'),'--output',str(dest)]
            run=subprocess.run(command,cwd=dest,check=True,capture_output=True,text=True)
            json.loads(run.stdout)
            for path in sorted(dest.rglob('*')):
                if not path.is_file():continue
                rel=path.relative_to(dest);require((ROOT/rel).read_bytes()==path.read_bytes(),'fresh rebuild mismatch: '+str(rel));count+=1
    receipt={'status':'PASS','local':local,'arithmetic_chain':chain,'printed_rows':n,'printed_mutations_rejected':1,
             'fresh_rebuild_files':count,'optimized_python':bool(sys.flags.optimize),
             'equation_sha256':hashlib.sha256((endpoint/'equation.json').read_bytes()).hexdigest(),
             'scope':'Exact finite algebra and frozen-source binding; ordinary unbounded proof remains separate.'}
    rendered=json.dumps(receipt,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(rendered)
    print(rendered,end='')
if __name__=='__main__':main()
