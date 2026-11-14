"use strict";
const fs=require("fs"),path=require("path"),crypto=require("crypto"),{fmt,rootfree}=require("./tm.js");
const dir=__dirname,sha=s=>crypto.createHash("sha256").update(s).digest("hex");
const fixtures=JSON.parse(fs.readFileSync(path.join(dir,"graph-fixtures.json"),"utf8")).fixtures;
const candidates=["HA","HAZ"].map(n=>JSON.parse(fs.readFileSync(path.join(dir,n+"-candidate.json"),"utf8")));
const keys=new Map(),results=[];
function decode(x){if(x.table.length!==1164)throw Error(x.name+": payload length");const rows={};for(let q=0;q<194;q++){rows[q]=[];for(let b=0;b<2;b++){const p=6*q+3*b,v=+x.table[p],t=parseInt(x.table.slice(p+1,p+3),36);if(v<0||v>3||t<0||t>194)throw Error(x.name+": malformed action");rows[q][b]=[v>>1,(v&1)?"R":"L",t];}}return rows;}
for(const x of fixtures.concat(candidates)){const rows=decode(x),text=fmt(rows),key=rootfree(rows);if(sha(text)!==x.normalized_sha256)throw Error(x.name+": normalized digest");if(sha(key)!==x.graph_sha256)throw Error(x.name+": graph digest");const disk=fs.readFileSync(path.join(dir,"tables",x.name+".tm"),"utf8");if(disk!==text)throw Error(x.name+": written table differs");keys.set(x.name,key);results.push({name:x.name,start:x.start,normalized_sha256:x.normalized_sha256,graph_sha256:x.graph_sha256});}
if(new Set(fixtures.map(x=>keys.get(x.name))).size!==fixtures.length)throw Error("Duplicate prior graph classes");
const matches={};for(const c of candidates){matches[c.name]=fixtures.filter(x=>keys.get(x.name)===keys.get(c.name)).map(x=>x.name);if(matches[c.name].length)throw Error(c.name+" already appears");}
console.log(JSON.stringify({prior_classes:fixtures.length,candidates:candidates.map(x=>x.name),candidate_matches:matches,results},null,2));
