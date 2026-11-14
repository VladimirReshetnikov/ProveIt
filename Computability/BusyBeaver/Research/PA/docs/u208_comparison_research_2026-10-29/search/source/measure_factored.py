import pathlib,json,subprocess
P=pathlib.Path('u208_reduction_20261029/source_search')
G=('Q','c',('I',('R','c','1'),('R','c','0')))
e=('R','1','c');L=('I',G,('I','c',e));U=('I',e,'c')
forms={'original':('Q','c',('I',('Q','1',L),('N',('Q','1',U)))),
       'factored_lower_first':('Q','c',('N',('Q','1',('N',('I',L,('N',U)))))),
       'factored_upper_first':('Q','c',('N',('Q','1',('N',('I',U,('N',L))))))}
def postfix(x):return[x]if isinstance(x,str)else sum((postfix(y)for y in x[1:]),[])+[x[0]]
base=(P/'measure_adjoin.py').read_text();out=[]
for name,x in forms.items():
 word=postfix(x);script=base.replace("word='c 1 1 0 R N 1 5 Eq I c 1 c R I I Q 1 1 c R c I Q N I Q'.split()",f'word={word!r}')
 script=script.replace("'adjoin_source.json'",repr(name+'_source.json')).replace("'adjoin_metrics.json'",repr(name+'_metrics.json'))
 q=P/(name+'_measure.py');q.write_text(script)
 r=subprocess.run(['python3',str(q)],capture_output=True,text=True);(P/(name+'_measure.log')).write_text(r.stdout+r.stderr);r.check_returncode();m=json.loads((P/(name+'_metrics.json')).read_text());out.append({'name':name,'postfix':word,**m})
(P/'factored_metrics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
