"use strict";
const fs=require("fs"),path=require("path"),crypto=require("crypto"),{parse,rootfree}=require("./tm.js");
const source=process.argv[2],output=process.argv[3],archive=process.argv[4]||path.basename(source);
const sha=s=>crypto.createHash("sha256").update(s).digest("hex");
function walk(dir){return fs.readdirSync(dir,{withFileTypes:true}).flatMap(e=>e.isDirectory()?walk(path.join(dir,e.name)):e.isFile()?[path.join(dir,e.name)]:[]);}
const files=walk(source).filter(p=>/\.(tm|txt)$/i.test(p)),groups=new Map(),state_counts={};let recognized=0;
for(const file of files){let text;try{text=fs.readFileSync(file,"utf8");}catch{continue;}const p=parse(text);if(!p.valid)continue;recognized++;const states=p.labels.length;state_counts[states]=(state_counts[states]||0)+1;const hash=sha(text);let record=groups.get(hash);if(!record){record={sha256:hash,states,rows:2*states,occurrences:[]};if(states<=194){const key=rootfree(p.rows);record.graph_sha256=key===null?null:sha(key);}groups.set(hash,record);}record.occurrences.push(path.relative(source,file));}
const rec={archive,candidate_files:files.length,recognized_tables:recognized,unique_byte_forms:groups.size,state_counts,recognized_le194:[...groups.values()].filter(x=>x.states<=194),all_byte_forms:[...groups.values()]};
fs.writeFileSync(output,JSON.stringify(rec,null,2)+"\n");console.log(JSON.stringify({archive,candidate_files:files.length,recognized_tables:recognized,unique_byte_forms:groups.size,state_counts,le194_unique:rec.recognized_le194.length}));
