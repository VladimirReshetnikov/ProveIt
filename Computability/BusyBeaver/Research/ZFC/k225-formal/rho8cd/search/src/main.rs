// Given-clause condensed-detachment search for the dominated Lukasiewicz calculus.
//
//   cdr MAXW MAXC BUDGET [CPEN [HINTS HW]]
//
// Axioms: Z (the code 0, Z = Z>Z) and ((p>q)>r)>((r>p)>(s>p)) under q <= r, a side condition
// discharged when q is Z or a subterm of r.  Goal: that row with no side condition.  Clauses
// carry at most MAXC open side conditions and MAXW tokens; the weight is the length plus CPEN per
// side condition, or HW when the clause generalizes a hint (Veroff's hints strategy).  Prints the
// proof DAG as `i major minor formula [conditions]`, read by ../generate_domrho8_cd.py.
// Environment: NOZ=1 drops the truth axiom Z; UNR=1 drops the side condition of the row; GOALS="F;G;..." adds goals (all must be proved;
// `#GOAL i F` lines name the lemma proving each).
// Untrusted: the kernels check the rendered derivation.
//
// Terms are Polish token vectors: 0 = Z, 1 = imp, v + 2 = variable v.
use std::collections::{BinaryHeap, HashSet};
use std::cmp::Reverse;

type Tm = Vec<u32>;
const ZT: u32 = 0;
const IM: u32 = 1;

#[derive(Clone)]
struct Thm { t: Tm, c: Vec<(Tm, Tm)>, maj: i64, min: i64 }

// ---------- tree arena for unification ----------
#[derive(Clone, Copy)]
enum N { Z, V(u32), I(usize, usize) }

struct Ar { n: Vec<N>, bind: Vec<Option<usize>> }

impl Ar {
    fn build(&mut self, t: &[u32], pos: &mut usize, off: u32) -> usize {
        let tok = t[*pos]; *pos += 1;
        match tok {
            ZT => { self.n.push(N::Z); self.n.len() - 1 }
            IM => { let a = self.build(t, pos, off); let b = self.build(t, pos, off); self.n.push(N::I(a, b)); self.n.len() - 1 }
            v => { let id = (v - 2 + off) as usize; self.n.push(N::V(id as u32)); if self.bind.len() <= id { self.bind.resize(id + 1, None); } self.n.len() - 1 }
        }
    }
    fn walk(&self, mut x: usize) -> usize {
        loop {
            match self.n[x] { N::V(v) => match self.bind[v as usize] { Some(y) => x = y, None => return x }, _ => return x }
        }
    }
    fn occurs(&self, v: u32, x: usize) -> bool {
        let x = self.walk(x);
        match self.n[x] { N::V(w) => w == v, N::I(a, b) => self.occurs(v, a) || self.occurs(v, b), N::Z => false }
    }
    fn unify(&mut self, x: usize, y: usize) -> bool {
        let mut st = vec![(x, y)];
        while let Some((x, y)) = st.pop() {
            let x = self.walk(x); let y = self.walk(y);
            if x == y { continue; }
            match (self.n[x], self.n[y]) {
                (N::V(v), N::V(w)) if v == w => {}
                (N::V(v), _) => { if self.occurs(v, y) { return false; } self.bind[v as usize] = Some(y); }
                (_, N::V(w)) => { if self.occurs(w, x) { return false; } self.bind[w as usize] = Some(x); }
                (N::Z, N::Z) => {}
                (N::Z, N::I(a, b)) => { st.push((x, a)); st.push((x, b)); }
                (N::I(a, b), N::Z) => { st.push((a, y)); st.push((b, y)); }
                (N::I(a, b), N::I(c, d)) => { st.push((a, c)); st.push((b, d)); }
            }
        }
        true
    }
    // extract normalized term (Z -> Z collapses to Z)
    fn ext(&self, x: usize, out: &mut Tm, depth: usize) -> bool {
        if depth > 200 || out.len() > 400 { return false; }
        let x = self.walk(x);
        match self.n[x] {
            N::Z => out.push(ZT),
            N::V(v) => out.push(v + 2),
            N::I(a, b) => {
                let s = out.len(); out.push(IM);
                if !self.ext(a, out, depth + 1) { return false; }
                if !self.ext(b, out, depth + 1) { return false; }
                if out.len() == s + 3 && out[s + 1] == ZT && out[s + 2] == ZT { out.truncate(s); out.push(ZT); }
            }
        }
        true
    }
}

fn span(t: &[u32], i: usize) -> usize { // end index of subterm starting at i
    let mut need = 1usize; let mut j = i;
    while need > 0 { if t[j] == IM { need += 2; } need -= 1; j += 1; }
    j
}
fn subterm(a: &[u32], b: &[u32]) -> bool {
    if a.len() > b.len() { return false; }
    let mut i = 0;
    while i + a.len() <= b.len() { if &b[i..i + a.len()] == a && span(b, i) == i + a.len() { return true; } i += 1; }
    false
}
fn vars(t: &[u32], acc: &mut Vec<u32>) { for &x in t { if x >= 2 && !acc.contains(&x) { acc.push(x); } } }
fn maxvar(t: &[u32]) -> u32 { t.iter().filter(|&&x| x >= 2).map(|&x| x - 1).max().unwrap_or(0) }

fn simp(t: &Tm, cs: Vec<(Tm, Tm)>) -> Option<Vec<(Tm, Tm)>> {
    let mut out: Vec<(Tm, Tm)> = vec![];
    for (a, b) in cs {
        if a == vec![ZT] || subterm(&a, &b) { continue; }
        if subterm(&b, &a) { return None; }
        if !out.contains(&(a.clone(), b.clone())) { out.push((a, b)); }
    }
    // dangling side-condition variables can be chosen freely
    loop {
        let mut drop = None;
        for k in 0..out.len() {
            let mut other = vec![]; vars(t, &mut other);
            for (m, (c, d)) in out.iter().enumerate() { if m != k { vars(c, &mut other); vars(d, &mut other); } }
            let (a, b) = &out[k];
            let da = a.len() == 1 && a[0] >= 2 && !other.contains(&a[0]) && !b.contains(&a[0]);
            let db = b.len() == 1 && b[0] >= 2 && !other.contains(&b[0]) && !a.contains(&b[0]);
            if da || db { drop = Some(k); break; }
        }
        match drop { Some(k) => { out.remove(k); } None => break }
    }
    Some(out)
}

fn canon(t: &Tm, cs: &Vec<(Tm, Tm)>) -> (Tm, Vec<(Tm, Tm)>) {
    let mut m: Vec<u32> = vec![];
    let r = |x: &Tm, m: &mut Vec<u32>| -> Tm { x.iter().map(|&y| if y >= 2 { match m.iter().position(|&z| z == y) { Some(p) => p as u32 + 2, None => { m.push(y); m.len() as u32 + 1 } } } else { y }).collect() };
    let t2 = r(t, &mut m);
    let mut c2: Vec<(Tm, Tm)> = cs.iter().map(|(a, b)| { let a2 = r(a, &mut m); let b2 = r(b, &mut m); (a2, b2) }).collect();
    c2.sort();
    (t2, c2)
}

fn matches(g: &[u32], t: &[u32]) -> bool {
    let mut bind: Vec<Option<(usize, usize)>> = vec![None; 64];
    let (mut i, mut j) = (0usize, 0usize);
    while i < g.len() {
        let x = g[i];
        if x >= 2 {
            let e = span(t, j);
            let v = (x - 2) as usize;
            if v >= bind.len() { bind.resize(v + 1, None); }
            match bind[v] { Some((a, b)) => { if t[a..b] != t[j..e] { return false; } } None => bind[v] = Some((j, e)) }
            i += 1; j = e;
        } else {
            if j >= t.len() || t[j] != x { return false; }
            i += 1; j += 1;
        }
    }
    true
}

fn show(t: &[u32]) -> String {
    fn go(t: &[u32], i: &mut usize, s: &mut String) {
        let x = t[*i]; *i += 1;
        match x { ZT => s.push('Z'), IM => { s.push('('); go(t, i, s); s.push('>'); go(t, i, s); s.push(')'); } v => s.push_str(&format!("{}", (b'a' + (v - 2) as u8) as char)) }
    }
    let mut s = String::new(); let mut i = 0; go(t, &mut i, &mut s); s
}

fn parse(s: &[u8], i: &mut usize, out: &mut Tm) {
    let c = s[*i];
    if c == b'(' { *i += 1; out.push(IM); parse(s, i, out); *i += 1; parse(s, i, out); *i += 1; }
    else if c == b'Z' { *i += 1; out.push(ZT); }
    else { *i += 1; out.push((c - b'a') as u32 + 2); }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let maxw: usize = args[1].parse().unwrap();
    let maxc: usize = args[2].parse().unwrap();
    let budget: usize = args[3].parse().unwrap();
    let cpen: usize = if args.len() > 4 { args[4].parse().unwrap() } else { 3 };
    let (p, q, r, s) = (2u32, 3u32, 4u32, 5u32);
    // ((p>q)>r)>((r>p)>(s>p))
    let ax: Tm = vec![IM, IM, IM, p, q, r, IM, IM, r, p, IM, s, p];
    let mut goals: Vec<Tm> = vec![ax.clone()];
    if let Ok(g) = std::env::var("GOALS") { for l in g.split(';').filter(|l| !l.is_empty()) { let mut o = vec![]; let mut i = 0; parse(l.as_bytes(), &mut i, &mut o); goals.push(o); } }
    let mut found: Vec<Option<usize>> = vec![None; goals.len()];
    let hints: Vec<Tm> = if args.len() > 5 { std::fs::read_to_string(&args[5]).unwrap().lines().filter(|l| !l.is_empty()).map(|l| { let mut o = vec![]; let mut i = 0; parse(l.as_bytes(), &mut i, &mut o); canon(&o, &vec![]).0 }).collect() } else { vec![] };
    let hw: usize = if args.len() > 6 { args[6].parse().unwrap() } else { 2 };
    eprintln!("hints {}", hints.len());
    let mut kept: Vec<Thm> = vec![];
    let mut seen: HashSet<(Tm, Vec<(Tm, Tm)>)> = HashSet::new();
    let mut heap: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
    let mut pend: Vec<Thm> = vec![];
    let push = |th: Thm, seen: &mut HashSet<(Tm, Vec<(Tm, Tm)>)>, heap: &mut BinaryHeap<Reverse<(usize, usize)>>, pend: &mut Vec<Thm>| {
        let (t, c) = canon(&th.t, &th.c);
        if t.len() > maxw || c.len() > maxc { return; }
        if !seen.insert((t.clone(), c.clone())) { return; }
        let hit = hints.iter().any(|h| matches(&t, h));
        let w = if hit { hw + cpen * c.len() } else { t.len() + cpen * c.len() };
        pend.push(Thm { t, c, maj: th.maj, min: th.min });
        heap.push(Reverse((w, pend.len() - 1)));
    };
    if std::env::var("NOZ").is_err() { push(Thm { t: vec![ZT], c: vec![], maj: -1, min: -1 }, &mut seen, &mut heap, &mut pend); }
    push(Thm { t: ax.clone(), c: if std::env::var("UNR").is_ok() { vec![] } else { vec![(vec![q], vec![r])] }, maj: -2, min: -2 }, &mut seen, &mut heap, &mut pend);
    let t0 = std::time::Instant::now();
    let mut steps = 0;
    while let Some(Reverse((_w, pi))) = heap.pop() {
        if steps >= budget { break; }
        let th = pend[pi].clone();
        if kept.iter().any(|k| k.c.is_empty() && k.t.len() <= th.t.len() && matches(&k.t, &th.t)) { continue; }
        kept.push(th.clone());
        let me = kept.len() - 1;
        if th.c.is_empty() {
            for (g, f) in goals.iter().zip(found.iter_mut()) { if f.is_none() && matches(&th.t, g) { *f = Some(me); } }
        }
        if found.iter().all(|f| f.is_some()) {
            // print the union proof DAG of all goals
            let mut need = vec![]; let mut st: Vec<usize> = found.iter().map(|f| f.unwrap()).collect();
            while let Some(i) = st.pop() { if need.contains(&i) { continue; } need.push(i); if kept[i].maj >= 0 { st.push(kept[i].maj as usize); st.push(kept[i].min as usize); } }
            need.sort();
            println!("PROOF {} steps={} kept={} secs={}", need.len(), steps, kept.len(), t0.elapsed().as_secs());
            for (g, f) in goals.iter().zip(found.iter()) { println!("#GOAL {} {}", f.unwrap(), show(g)); }
            for i in need {
                let k = &kept[i];
                let cs: Vec<String> = k.c.iter().map(|(a, b)| format!("{}<={}", show(a), show(b))).collect();
                println!("{} {} {} {} [{}]", i, k.maj, k.min, show(&k.t), cs.join(","));
            }
            return;
        }
        steps += 1;
        for j in 0..kept.len() {
            for &(mi, ni) in &[(me, j), (j, me)] {
                if mi == ni && j != me { continue; }
                let (mt, nt) = (&kept[mi], &kept[ni]);
                if mt.t[0] != IM && mt.t[0] != ZT { continue; }
                let off = maxvar(&mt.t).max(mt.c.iter().map(|(a, b)| maxvar(a).max(maxvar(b))).max().unwrap_or(0));
                let mut ar = Ar { n: vec![], bind: vec![] };
                let mut pos = 0; let mroot = ar.build(&mt.t, &mut pos, 0);
                let mut pos = 0; let nroot = ar.build(&nt.t, &mut pos, off);
                let mc: Vec<(usize, usize)> = mt.c.iter().map(|(a, b)| { let mut p1 = 0; let x = ar.build(a, &mut p1, 0); let mut p2 = 0; let y = ar.build(b, &mut p2, 0); (x, y) }).collect();
                let nc: Vec<(usize, usize)> = nt.c.iter().map(|(a, b)| { let mut p1 = 0; let x = ar.build(a, &mut p1, off); let mut p2 = 0; let y = ar.build(b, &mut p2, off); (x, y) }).collect();
                let (xa, yb) = match ar.n[mroot] { N::I(a, b) => (a, b), N::Z => (mroot, mroot), _ => continue };
                if !ar.unify(xa, nroot) { continue; }
                let mut res = vec![]; if !ar.ext(yb, &mut res, 0) { continue; }
                if res.len() > maxw { continue; }
                let mut cs = vec![];
                let mut ok = true;
                for &(x, y) in mc.iter().chain(nc.iter()) {
                    let mut a = vec![]; let mut b = vec![];
                    if !ar.ext(x, &mut a, 0) || !ar.ext(y, &mut b, 0) { ok = false; break; }
                    cs.push((a, b));
                }
                if !ok { continue; }
                let cs = match simp(&res, cs) { Some(c) => c, None => continue };
                push(Thm { t: res, c: cs, maj: mi as i64, min: ni as i64 }, &mut seen, &mut heap, &mut pend);
            }
        }
        if steps % 1000 == 0 { let cov = hints.iter().filter(|h| kept.iter().any(|k| k.c.is_empty() && matches(&k.t, h))).count(); eprintln!("cov {}/{}", cov, hints.len()); }
        if steps % 1000 == 0 { eprintln!("{} kept={} pend={} w={} {}s", steps, kept.len(), heap.len(), _w, t0.elapsed().as_secs()); }
    }
    println!("NO PROOF steps={} kept={}", steps, kept.len());
}
