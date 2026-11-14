#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";
const here=path.dirname(fileURLToPath(import.meta.url));
const audit=JSON.parse(fs.readFileSync(path.join(here,"transition_graphs.json"),"utf8"));
const code=audit.code.parse_numeric_table_javascript+"\n"+audit.code.canonical_javascript+"\n"+audit.code.sha256_ascii_javascript;
const check=new Function("audit",code+`
const seen=new Map(),result={tables:0,classes:0,candidates:[]};
for(const item of audit.tables){
 if(sha256(item.table)!==item.sha256)throw Error("Table digest");
 const t=parseTM(item.table);if(!t||t.size!==194)throw Error("Invalid table");
 const c=canonical(t);if(!c.key||sha256(c.key)!==item.graph_sha256)throw Error("Graph digest");
 seen.set(c.key,true);result.tables++;
}
result.classes=seen.size;
if(result.tables!==51||result.classes!==28)throw Error("Corpus counts");
for(const item of audit.candidates){
 const t=parseTM(item.table),c=canonical(t);
 if(sha256(item.table)!==item.sha256||sha256(c.key)!==item.graph_sha256)throw Error("Candidate digest");
 if(seen.has(c.key))throw Error("Not novel");
 result.candidates.push({name:item.name,graph_sha256:item.graph_sha256,novel:true});
}return result;
`);
console.log(JSON.stringify(check(audit),null,2));
