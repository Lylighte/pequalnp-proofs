'use strict';
// Rebuild one previously excluded orbit, retain its binary LRAT, and verify it.
// Run: D:\\pequalnp-agent\\tools\\node\\node.exe reproduce.cjs
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const {spawnSync} = require('node:child_process');
const dir = __dirname;
const state = path.dirname(dir);
const root = path.dirname(state);
const upstream = path.join(state,'petersen-struct');
const tools = path.join(root,'tools','elan','toolchains','leanprover--lean4---v4.36.0','bin');
const sha = data => crypto.createHash('sha256').update(data).digest('hex');
const fresh = path.join(dir,'regenerated');
fs.mkdirSync(fresh,{recursive:true});
fs.copyFileSync(path.join(upstream,'synthesis.cjs'),path.join(fresh,'synthesis.cjs'));
const generate = spawnSync(process.execPath,[path.join(fresh,'synthesis.cjs')],{encoding:'utf8',windowsHide:true});
assert.equal(generate.status,0,generate.stderr);
for (const file of ['six-gates.cnf','six-gates-selectors.json'])
  assert(fs.readFileSync(path.join(fresh,file)).equals(fs.readFileSync(path.join(upstream,file))));
const base = fs.readFileSync(path.join(fresh,'six-gates.cnf'),'utf8');
const selectors = JSON.parse(fs.readFileSync(path.join(fresh,'six-gates-selectors.json'),'utf8'));
const fingerprint = sha(base + JSON.stringify(selectors));
const pin = {l:15,r:593,id:'15-593'};
const rows = fs.readFileSync(path.join(state,'petersen-orbits','results.jsonl'),'utf8').trimEnd().split('\n');
const entry = rows.map(s=>JSON.parse(s)).find(r=>r.id===pin.id && r.result==='UNSAT' && r.fingerprint===fingerprint);
assert(entry && entry.l===pin.l && entry.r===pin.r);
const pins = selectors.gates[0].flatMap((side,j)=>side.map((v,i)=>((j?pin.r:pin.l)&(1<<i))?v:-v));
assert.equal(pins.length,20);
const cnf = base.replace(/^p cnf (\d+) (\d+)/,(_,v,c)=>'p cnf '+v+' '+(Number(c)+pins.length)) + pins.map(v=>v+' 0\n').join('');
const inName=path.join(dir,'orbit-15-593.cnf'), proofName=path.join(dir,'orbit-15-593.lrat');
fs.writeFileSync(inName,cnf);
const start=Date.now();
const solve=spawnSync(path.join(tools,'cadical.exe'),['-q','--lrat','--binary','-c','150000',inName,proofName],{encoding:'utf8',timeout:45000,windowsHide:true});
const solverMs=Date.now()-start;
assert.equal(solve.status,20,solve.stderr+' '+solve.stdout);
assert.match(solve.stdout,/^s UNSATISFIABLE\s*$/m);
const verifyStart=Date.now();
const checked=spawnSync(path.join(tools,'lean.exe'),['--run',path.join(dir,'Check.lean'),inName,proofName],{cwd:dir,encoding:'utf8',timeout:60000,windowsHide:true});
const checkerMs=Date.now()-verifyStart;
assert.equal(checked.status,0,checked.stdout+' '+checked.stderr);
const verifier=JSON.parse(checked.stdout.trim());
const proof=fs.readFileSync(proofName);
const report={id:pin.id,orbitSize:entry.size,rawFingerprint:fingerprint,cnfBytes:Buffer.byteLength(cnf),cnfSHA256:sha(cnf),
  lratBytes:proof.length,lratSHA256:sha(proof),solverMs,checkerMs,verifier,common:'Runtime computed by the Lean Std LRAT checker. No new kernel theorem on this CNF or circuit encoding is claimed.'};
fs.writeFileSync(path.join(dir,'result.json'),JSON.stringify(report,null,2)+'\n');
console.log(report);
