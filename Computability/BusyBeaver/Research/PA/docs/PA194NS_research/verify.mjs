#!/usr/bin/env node
// Node.js >=18. This wraps the independently executed verification_core.js.
// This file I/O wrapper and its core both ran successfully in the producing session.
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import {fileURLToPath} from "node:url";
const root=path.dirname(fileURLToPath(import.meta.url));
const read=p=>fs.readFileSync(path.join(root,p),"utf8");
const core=read("verification_core.js");
const check=new Function("files",core+String.raw`
const nd=parseProgram(files["reference/PA196/Program.lean"]),g=JSON.parse(files["baseline/grammar.json"]),results={};
for(const name of ["primary","pa194sums","pa194ns"]){
 const patch=name==="primary"?{}:{node168:["node37","node56"],node171:["node170",[["leaf","inc",5],["leaf","continueTo",3]]]};
 if(name==="pa194ns")patch.node163=["node6","node54"];
 const s=sourceFrom(nd,g,patch),tab=files[name==="primary"?"baseline/pa194.native.tm":name+".native.tm"];
 results[name]={source_sites:s.sites.length,...validate(parseTable(tab),s.sites,s.instructions)};
}return results;
`);
const paths=["reference/PA196/Program.lean","baseline/grammar.json","baseline/pa194.native.tm","pa194sums.native.tm","pa194ns.native.tm"];
const files=Object.fromEntries(paths.map(p=>[p,read(p)])),result=check(files);
const expected=JSON.parse(read("evidence/v8_replay.json"));
if(JSON.stringify(result)!==JSON.stringify(expected))throw Error("Symbolic receipt mismatch");
for(const [name,wanted] of Object.entries({
 "pa194sums.native.tm":"b81a833dc99bcc2204ba513260e2e4fa07981b018228eef2f0bcc188e977f9c2",
 "pa194ns.native.tm":"db2ce84a0e883b44e348b60c834382245a9f55623de675ffdacb1e8b3c18bf75",
 "pa194sums.tm":"f7c8799c86847a4aeb85f078015f159a6fabbc94d5e26cbd84f337c4f8789fa8",
 "pa194ns.tm":"eef9329b9a7e1f2810eddcf3e99fc0184b073ea266d658ebe473f7d11d68ecd7"
}))if(crypto.createHash("sha256").update(read(name)).digest("hex")!==wanted)throw Error("Hash mismatch: "+name);
console.log(JSON.stringify(result,null,2));
