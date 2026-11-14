// Optional timed research replay. Recorded counts vary with hardware/runtime.
// node replay_order_search.mjs [milliseconds=22000] [seed=71478]
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const dir=path.dirname(fileURLToPath(import.meta.url));
const data=JSON.parse(fs.readFileSync(path.join(dir,'data.json'),'utf8'));
const load=key=>data[key];
const text=value=>console.log(JSON.stringify(value));
const notify=text;
const millis=Number(process.argv[2]??22000);
const seed=Number(process.argv[3]??71478);
const source=fs.readFileSync(path.join(dir,'optimizer_core.js'),'utf8')+'\n'+fs.readFileSync(path.join(dir,'annealing.js'),'utf8');
eval(source+'\ntext(optimize(load("order-seeds"),millis,seed));');
