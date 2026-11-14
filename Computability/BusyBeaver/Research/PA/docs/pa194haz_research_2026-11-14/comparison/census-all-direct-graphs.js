"use strict";
const fs=require("fs"),path=require("path"),crypto=require("crypto"),{parse,rootfree}=require("./tm.js");
const root=__dirname,manifest=JSON.parse(fs.readFileSync(path.join(root,"direct-tm-file-manifest.json"),"utf8"));
const groups=new Map(),byStates={},unclassified=[];
for(let i=0;i<manifest.length;i++){const m=manifest[i];if(!m.valid)continue;const text=fs.readFileSync(path.join(root,"raw-tables",m.blob+".tm"),"utf8"),p=parse(text);if(!p.valid||p.labels.length!==m.states)throw Error(m.blob);
const key=rootfree(p.rows);if(key===null){unclassified.push({blob:m.blob,states:m.states,reason:"No control reaches all declared working controls"});continue;}const hash=crypto.createHash("sha256").update(key).digest("hex");let g=groups.get(hash);if(!g){g={states:m.states,graph_sha256:hash,blobs:[],occurrences:0};groups.set(hash,g);}g.blobs.push(m.blob);g.occurrences+=m.paths.filter(p=>p.endsWith(".tm")).length;
}
for(const g of groups.values())byStates[g.states]=(byStates[g.states]||0)+1;
const result={scope:"Direct .tm files in 41 placed packets; one-halt complete numeric binary tables; all spanning roots, symbol complement, reflection",snapshot:"1e407ae841e4666f932777fad977ba784ebbcfd5",recognized_blobs:manifest.filter(m=>m.valid).length,classes:groups.size,unclassified,class_counts_by_states:byStates,graph_classes:[...groups.values()]};
fs.writeFileSync(path.join(root,"direct-graph-census.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify({recognized_blobs:result.recognized_blobs,classes:result.classes,unclassified:result.unclassified,class_counts_by_states:byStates}));
