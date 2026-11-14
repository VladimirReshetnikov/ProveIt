import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const dir=path.dirname(fileURLToPath(import.meta.url));
const data=JSON.parse(fs.readFileSync(path.join(dir,'data.json'),'utf8'));
const load=key=>data[key];
const text=value=>console.log(JSON.stringify(value));
const notify=text;
const source=fs.readFileSync(path.join(dir,'optimizer_core.js'),'utf8');
eval(source+String.raw`
for (const [name,g] of [['principal',load('primarygrammar')],['GammaH-best',JSON.parse(load('Hsource-2').value.structuredContent.content)],['GammaH-adaptive',JSON.parse(load('Hsource-1').value.structuredContent.content)]]) {
 const r=loadg(g),v=calc(r),f=compatible(v);text({name,fixed:134,raw_readers:v.n,matching_bound:v.fold,compatible_folds:f.length,states:134+v.n-f.length,penalty:v.pen,local_cases:4*f.length});
}
`);

