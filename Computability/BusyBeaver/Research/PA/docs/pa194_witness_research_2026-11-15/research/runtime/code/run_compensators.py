from pathlib import Path
import subprocess,json,time,sys
here=Path(__file__).resolve().parent
synth=Path(sys.argv[4]).resolve() if len(sys.argv)>4 else here/'merge_compensated'
table=Path(sys.argv[1]);patterns=Path(sys.argv[2]);out=Path(sys.argv[3]);out.mkdir(exist_ok=True)
states=sorted({int(x.split()[0])for x in table.read_text().splitlines()})
start=time.monotonic();records=[]
for q in states:
 if q in(301,88):continue
 for b in(0,1):
  p=subprocess.run([str(synth),str(table),'6','160',str(patterns),'301','88',str(q),str(b)],capture_output=True,text=True,check=True)
  (out/f'{q}_{b}.log').write_text(p.stderr)
  if p.stdout:(out/f'{q}_{b}.hits.jsonl').write_text(p.stdout)
  record={'q':q,'bit':b,'hits':len(p.stdout.splitlines()),'summary':p.stderr.splitlines()[-1]};records.append(record)
  if len(records)%25==0:print(json.dumps({'count':len(records),'hits':sum(r['hits']for r in records),'seconds':time.monotonic()-start}),flush=True)
(out/'summary.json').write_text(json.dumps({'rows':len(records),'hits':sum(r['hits']for r in records),'seconds':time.monotonic()-start,'results':records},indent=2)+'\n')
print(json.dumps({'rows':len(records),'hits':sum(r['hits']for r in records),'seconds':time.monotonic()-start}))
