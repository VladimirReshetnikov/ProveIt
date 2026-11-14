"use strict";
const fs=require("fs"),path=require("path"),crypto=require("crypto"),{parse,rootfree}=require("./tm.js");
const root=__dirname,sha=b=>crypto.createHash("sha256").update(b).digest("hex"),manifest=JSON.parse(fs.readFileSync(path.join(root,"combined-source-manifest.json"),"utf8"));
const exactGroups=new Map(),state_counts={},unclassified=[],excluded=[],byFile=[];let recognized=0,recognizedOccurrences=0,occurrences=0;
for(const m of manifest.files){const data=fs.readFileSync(path.join(root,m.raw_path));if(sha(data)!==m.sha256)throw Error("raw digest "+m.raw_path);const p=parse(data.toString("utf8"));if(p.labels.length!==m.states||p.valid!==m.recognized)throw Error("parser disagreement");const count=m.sources.length;occurrences+=count;
if(!p.valid){excluded.push({sha256:m.sha256,states:m.states,occurrences:count,halt_targets:p.halts,reason:"Outside complete one-halt-target recognizer",sources:m.sources});continue;}
recognized++;recognizedOccurrences+=count;const bucket=state_counts[m.states]||(state_counts[m.states]={unique_byte_forms:0,occurrences:0,spanning_graph_classes:0});bucket.unique_byte_forms++;bucket.occurrences+=count;
const key=rootfree(p.rows);if(key===null){unclassified.push({sha256:m.sha256,states:m.states,occurrences:count,reason:"No root reaches every declared working control",sources:m.sources});byFile.push({sha256:m.sha256,states:m.states,graph_sha256:null});continue;}
let g=exactGroups.get(key);if(!g){g={states:m.states,graph_sha256:sha(key),sha256s:[],occurrences:0};exactGroups.set(key,g);bucket.spanning_graph_classes++;}
g.sha256s.push(m.sha256);g.occurrences+=count;byFile.push({sha256:m.sha256,states:m.states,graph_sha256:g.graph_sha256});
}
const fixtureData=JSON.parse(fs.readFileSync(path.join(root,"graph-fixtures.json"),"utf8")).fixtures,prior194=[...exactGroups.values()].filter(g=>g.states===194);
if(prior194.length!==fixtureData.length)throw Error("194 corpus class count changed");
for(const g of prior194)if(!fixtureData.some(f=>f.graph_sha256===g.graph_sha256))throw Error("194 fixture missing");
const result={snapshot:manifest.snapshot,scope:manifest.scope,complete_numeric_occurrences:occurrences,complete_numeric_byte_forms:manifest.files.length,recognized_occurrences:recognizedOccurrences,recognized_byte_forms:recognized,spanning_byte_forms:recognized-unclassified.length,spanning_graph_classes:exactGroups.size,state_counts,excluded,unclassified,graph_classes:[...exactGroups.values()],byte_form_classes:byFile,archive_summaries:manifest.archive_summaries};
fs.writeFileSync(path.join(root,"combined-corpus-census.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify({complete_numeric_occurrences:occurrences,complete_numeric_byte_forms:manifest.files.length,recognized_occurrences:recognizedOccurrences,recognized_byte_forms:recognized,spanning_byte_forms:result.spanning_byte_forms,spanning_graph_classes:result.spanning_graph_classes,state_counts,excluded:excluded.map(x=>({states:x.states,occurrences:x.occurrences})),unclassified:unclassified.map(x=>({states:x.states,occurrences:x.occurrences}))}));
