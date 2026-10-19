import json,pathlib,sys
here=pathlib.Path(__file__).resolve().parent
p=pathlib.Path(sys.argv[1]);d=json.loads(p.read_text());n=d['states'];labels=[6,9,13,19,29,41,58,74][:n];mapping={i:q for i,q in enumerate(labels)}|{n:4,n+1:84,n+2:2,n+3:20,n+4:10,n+5:14}
table={}
for l in (here/'recovered/63/machine/zfc_prefix246_old.tm').read_text().splitlines():
 if l.startswith('#'):continue
 q,b,w,m,t=l.split();table[int(q),int(b)]=(int(w),m,int(t))
for q in [6,9,13,19,29,41,58,74][n:]:
 for b in [0,1]:del table[q,b]
for q,b,w,m,t in d['table']:table[mapping[q],b]=(w,m,mapping[t])
text='#! start 95\n'+''.join(f'{q} {b} {w} {m} {t}\n'for (q,b),(w,m,t)in sorted(table.items()))
out=p.with_suffix('.tm');out.write_text(text);print(out)
