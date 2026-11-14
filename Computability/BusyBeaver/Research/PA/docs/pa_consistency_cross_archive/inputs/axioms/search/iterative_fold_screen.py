from support import *
p=(INC,INC);c.MACROS[p]=99;c.MACROS[(p,p)]=190
if __name__=='__main__':
 import sys
 files=sys.argv[1:]or sorted(str(p)for p in Path('ties').glob('alltie_*.grammar.json'))+['scanner_6.grammar.json'];locals=0
 for f in files:
  t=c.read_grammar(f);r,i,s=c.build(t);ch=bestcompatible_all(r,s);rr,al=apply(r,ch);remaining={q:v for q,v in s.items() if q not in al};more=bestcompatible_all(rr,remaining)
  if more:
   locals+=1;print('LOCAL',f,len(more),more,flush=True);trial,aliases=apply(rr,more);ss,ins,cs=c.source(t);check=c.validate(trial,cs);print('CHECK',check,flush=True)
   if check['ok']:
    Path('iterative195.grammar.json').write_text(Path(f).read_text());Path('iterative195.folds.json').write_text(json.dumps([ch,more],indent=2));Path('iterative195.validation.json').write_text(json.dumps(check,indent=2));Path('iterative195.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(trial.items())));raise SystemExit('FOUND195')
 print('FINISHED',len(files),'locally improving',locals)
