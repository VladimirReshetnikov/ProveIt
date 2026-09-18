//! Khovanov homology over F2 by scanning (Bar-Natan's local algorithm).
//!
//! The partial complex of the processed region has objects (boundary matching,
//! homological degree) and morphisms that are F2-combinations of dotted
//! canonical cobordisms.  Representation choices made for Rust:
//!
//! * matchings are interned; everything downstream works with `u32` ids;
//! * a morphism of Hom(a, b) is a bitset over monomials (dot masks of the
//!   circles of a u b~): one inline `u64` when there are at most six circles,
//!   boxed words otherwise;
//! * the dot-independent topology of a gluing is compiled once into a plan of
//!   components `(left mask, right mask, boundary mask, extra dots)`;
//! * composition results and crossing transfers are memoized per stage;
//! * cancellation picks the pivot with the smallest Markowitz count through a
//!   lazy binary heap; over F2 a unit of End(m) is its own inverse.

use crate::filters::SMOOTHINGS;
use crate::util::{Dsu, FxMap, FxSet};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

pub type Pair = (u32, u32);
type MId = u32;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Morph {
    S(u64),
    B(Box<[u64]>),
}

impl Morph {
    fn zero(circles: usize) -> Morph {
        if circles <= 6 { Morph::S(0) } else { Morph::B(vec![0u64; 1 << (circles - 6)].into_boxed_slice()) }
    }
    fn one(circles: usize) -> Morph {
        let mut m = Morph::zero(circles);
        m.toggle(0);
        m
    }
    #[inline]
    fn toggle(&mut self, monomial: u32) {
        match self {
            Morph::S(w) => *w ^= 1u64 << monomial,
            Morph::B(ws) => ws[(monomial >> 6) as usize] ^= 1u64 << (monomial & 63),
        }
    }
    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            Morph::S(w) => *w == 0,
            Morph::B(ws) => ws.iter().all(|&w| w == 0),
        }
    }
    #[inline]
    fn is_unit(&self) -> bool {
        match self {
            Morph::S(w) => w & 1 == 1,
            Morph::B(ws) => ws[0] & 1 == 1,
        }
    }
    fn is_one(&self) -> bool {
        match self {
            Morph::S(w) => *w == 1,
            Morph::B(ws) => ws[0] == 1 && ws[1..].iter().all(|&w| w == 0),
        }
    }
    fn xor_assign(&mut self, other: &Morph) {
        match (self, other) {
            (Morph::S(a), Morph::S(b)) => *a ^= *b,
            (Morph::B(a), Morph::B(b)) => a.iter_mut().zip(b.iter()).for_each(|(x, y)| *x ^= *y),
            _ => unreachable!("morphisms of one Hom space share a representation"),
        }
    }
    fn monomials(&self, out: &mut Vec<u32>) {
        out.clear();
        match self {
            Morph::S(w) => {
                let mut w = *w;
                while w != 0 {
                    out.push(w.trailing_zeros());
                    w &= w - 1;
                }
            }
            Morph::B(ws) => {
                for (i, &word) in ws.iter().enumerate() {
                    let mut w = word;
                    while w != 0 {
                        out.push((i as u32) << 6 | w.trailing_zeros());
                        w &= w - 1;
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
struct Comp {
    left: u32,
    right: u32,
    boundary: u32,
    extra: u8,
}

struct Basis {
    owner: Vec<(u32, u8)>, // sorted by boundary label
    count: usize,
}

impl Basis {
    #[inline]
    fn circle(&self, point: u32) -> usize {
        let i = self.owner.binary_search_by_key(&point, |&(p, _)| p).expect("point of the basis");
        self.owner[i].1 as usize
    }
}

#[derive(Clone, Copy)]
enum Target {
    New(u32),
    Closed(u8),
}

struct Glued {
    matching: MId,
    closed: u8,
    m_arc: Vec<Target>,
    s_arc: [Target; 2],
}

struct TransferPlan {
    circles_out: usize,
    plans: Vec<(u8, u8, Vec<Comp>)>,
}

#[derive(Default, Clone, Debug)]
pub struct Stats {
    pub max_boundary: usize,
    pub max_objects_before: usize,
    pub max_objects_after: usize,
    pub eliminations: u64,
    pub compose_calls: u64,
    pub compose_cache_hits: u64,
    pub compose_shortcuts: u64,
    pub plans: u64,
    pub transfer_plans: u64,
    pub matchings: usize,
    pub time_transfer: Duration,
    pub time_eliminate: Duration,
    pub time_linear: Duration,
}

struct Algebra {
    matchings: Vec<Rc<Vec<Pair>>>,
    index: FxMap<Rc<Vec<Pair>>, MId>,
    bases: FxMap<(MId, MId), Rc<Basis>>,
    plans: FxMap<(MId, MId, MId), Option<Rc<Vec<Comp>>>>,
    composed: FxMap<(MId, MId, MId, Morph, Morph), Morph>,
    glued: FxMap<(MId, u8), Rc<Glued>>,
    transfer_plans: FxMap<(MId, MId, u8, u8), Rc<TransferPlan>>,
    transferred: FxMap<(MId, MId, Morph, u8, u8), Rc<Vec<(u8, u8, Morph)>>>,
    scratch_f: Vec<u32>,
    scratch_g: Vec<u32>,
    stats: Stats,
}

fn evaluate(plan: &[Comp], tf: u32, tg: u32, acc: &mut Morph, work: &mut Vec<u32>, next: &mut Vec<u32>) {
    work.clear();
    work.push(0);
    for c in plan {
        let dots = (tf & c.left).count_ones() + (tg & c.right).count_ones() + c.extra as u32;
        if dots >= 2 {
            return;
        }
        if c.boundary == 0 {
            if dots != 1 {
                return;
            }
            continue;
        }
        if dots == 1 {
            for m in work.iter_mut() {
                *m |= c.boundary;
            }
        } else {
            next.clear();
            let mut rest = c.boundary;
            while rest != 0 {
                let bit = rest & rest.wrapping_neg();
                let choice = c.boundary ^ bit;
                for &m in work.iter() {
                    next.push(m | choice);
                }
                rest ^= bit;
            }
            std::mem::swap(work, next);
        }
    }
    for &m in work.iter() {
        acc.toggle(m);
    }
}

impl Algebra {
    fn new() -> Self {
        Algebra {
            matchings: Vec::new(),
            index: FxMap::default(),
            bases: FxMap::default(),
            plans: FxMap::default(),
            composed: FxMap::default(),
            glued: FxMap::default(),
            transfer_plans: FxMap::default(),
            transferred: FxMap::default(),
            scratch_f: Vec::new(),
            scratch_g: Vec::new(),
            stats: Stats::default(),
        }
    }

    fn clear_stage(&mut self) {
        self.bases.clear();
        self.plans.clear();
        self.composed.clear();
        self.glued.clear();
        self.transfer_plans.clear();
        self.transferred.clear();
    }

    fn intern(&mut self, mut pairs: Vec<Pair>) -> MId {
        pairs.sort_unstable();
        let key = Rc::new(pairs);
        if let Some(&id) = self.index.get(&key) {
            return id;
        }
        let id = self.matchings.len() as MId;
        self.matchings.push(key.clone());
        self.index.insert(key, id);
        id
    }

    fn basis(&mut self, a: MId, b: MId) -> Rc<Basis> {
        if let Some(found) = self.bases.get(&(a, b)) {
            return found.clone();
        }
        let ma = self.matchings[a as usize].clone();
        let mb = self.matchings[b as usize].clone();
        let mut points: Vec<u32> = ma.iter().flat_map(|&(p, q)| [p, q]).collect();
        points.sort_unstable();
        let local = |p: u32| points.binary_search(&p).expect("matchings over the same points");
        let mut dsu = Dsu::new(points.len());
        for &(p, q) in ma.iter().chain(mb.iter()) {
            dsu.union(local(p), local(q));
        }
        // circles numbered by their smallest boundary label
        let mut circle_of_root: FxMap<usize, u8> = FxMap::default();
        let mut owner = Vec::with_capacity(points.len());
        for (i, &p) in points.iter().enumerate() {
            let root = dsu.find(i);
            let next = circle_of_root.len() as u8;
            let circle = *circle_of_root.entry(root).or_insert(next);
            owner.push((p, circle));
        }
        let basis = Rc::new(Basis { owner, count: circle_of_root.len() });
        self.bases.insert((a, b), basis.clone());
        self.bases.insert((b, a), basis.clone());
        basis
    }

    fn plan(&mut self, a: MId, b: MId, c: MId) -> Option<Rc<Vec<Comp>>> {
        if let Some(found) = self.plans.get(&(a, b, c)) {
            return found.clone();
        }
        self.stats.plans += 1;
        let (ab, bc, ac) = (self.basis(a, b), self.basis(b, c), self.basis(a, c));
        let (na, nb) = (ab.count, bc.count);
        let mut dsu = Dsu::new(na + nb);
        let mb = self.matchings[b as usize].clone();
        for &(p, _) in mb.iter() {
            dsu.union(ab.circle(p), na + bc.circle(p));
        }
        let mut gluings = vec![0i32; na + nb];
        for &(p, _) in mb.iter() {
            let r = dsu.find(ab.circle(p));
            gluings[r] += 1;
        }
        let mut discs = vec![0i32; na + nb];
        let mut left = vec![0u32; na + nb];
        let mut right = vec![0u32; na + nb];
        for i in 0..na {
            let r = dsu.find(i);
            discs[r] += 1;
            left[r] |= 1 << i;
        }
        for i in 0..nb {
            let r = dsu.find(na + i);
            discs[r] += 1;
            right[r] |= 1 << i;
        }
        let mut boundary = vec![0u32; na + nb];
        for &(p, _) in self.matchings[a as usize].clone().iter() {
            let r = dsu.find(ab.circle(p));
            boundary[r] |= 1 << ac.circle(p);
        }
        for &(p, _) in self.matchings[c as usize].clone().iter() {
            let r = dsu.find(na + bc.circle(p));
            boundary[r] |= 1 << ac.circle(p);
        }
        let mut comps = Vec::new();
        let mut zero = false;
        for r in 0..na + nb {
            if discs[r] == 0 {
                continue;
            }
            let twice_genus = 2 - (discs[r] - gluings[r]) - boundary[r].count_ones() as i32;
            assert!(twice_genus >= 0 && twice_genus % 2 == 0, "impossible surface component in a composition");
            if twice_genus > 0 {
                zero = true;
                break;
            }
            comps.push(Comp { left: left[r], right: right[r], boundary: boundary[r], extra: 0 });
        }
        let result = if zero { None } else { Some(Rc::new(comps)) };
        self.plans.insert((a, b, c), result.clone());
        result
    }

    /// g o f for f in Hom(a, b), g in Hom(b, c).
    fn compose(&mut self, f: &Morph, g: &Morph, a: MId, b: MId, c: MId) -> Morph {
        self.stats.compose_calls += 1;
        if a == b && f.is_one() {
            self.stats.compose_shortcuts += 1;
            return g.clone();
        }
        if b == c && g.is_one() {
            self.stats.compose_shortcuts += 1;
            return f.clone();
        }
        let key = (a, b, c, f.clone(), g.clone());
        if let Some(found) = self.composed.get(&key) {
            self.stats.compose_cache_hits += 1;
            return found.clone();
        }
        let circles = self.basis(a, c).count;
        let mut result = Morph::zero(circles);
        if let Some(plan) = self.plan(a, b, c) {
            let mut fs = std::mem::take(&mut self.scratch_f);
            let mut gs = std::mem::take(&mut self.scratch_g);
            f.monomials(&mut fs);
            g.monomials(&mut gs);
            let (mut work, mut next) = (Vec::with_capacity(8), Vec::with_capacity(8));
            for &tf in &fs {
                for &tg in &gs {
                    evaluate(&plan, tf, tg, &mut result, &mut work, &mut next);
                }
            }
            self.scratch_f = fs;
            self.scratch_g = gs;
        }
        self.composed.insert(key, result.clone());
        result
    }

    fn glue(&mut self, m: MId, smoothing: u8, on_boundary: &[bool], slots: [u32; 4]) -> Rc<Glued> {
        if let Some(found) = self.glued.get(&(m, smoothing)) {
            return found.clone();
        }
        let pairs = self.matchings[m as usize].clone();
        let np = 2 * pairs.len();
        // nodes: 2t, 2t+1 are the ends of pair t; np + j is slot j
        #[derive(Clone, Copy)]
        struct Edge {
            a: usize,
            b: usize,
            arc: i32, // >= 0: m-arc t; -1, -2: smoothing arc 0, 1; -3: identification
        }
        let mut edges: Vec<Edge> = Vec::with_capacity(pairs.len() + 6);
        for t in 0..pairs.len() {
            edges.push(Edge { a: 2 * t, b: 2 * t + 1, arc: t as i32 });
        }
        for (j, &(s, t)) in SMOOTHINGS[smoothing as usize].iter().enumerate() {
            edges.push(Edge { a: np + s, b: np + t, arc: -1 - j as i32 });
        }
        let label_of = |node: usize| if node < np { if node % 2 == 0 { pairs[node / 2].0 } else { pairs[node / 2].1 } } else { slots[node - np] };
        for j in 0..4 {
            let label = slots[j];
            if on_boundary[label as usize] {
                let node = (0..np).find(|&x| label_of(x) == label).expect("boundary label of the matching");
                edges.push(Edge { a: np + j, b: node, arc: -3 });
            } else if let Some(j0) = (0..j).find(|&x| slots[x] == label) {
                edges.push(Edge { a: np + j, b: np + j0, arc: -3 });
            }
        }
        let total = np + 4;
        let mut adjacency: Vec<Vec<usize>> = vec![Vec::with_capacity(2); total];
        for (i, e) in edges.iter().enumerate() {
            adjacency[e.a].push(i);
            adjacency[e.b].push(i);
        }
        let mut visited = vec![false; total];
        let mut m_arc = vec![Target::Closed(0); pairs.len()];
        let mut s_arc = [Target::Closed(0); 2];
        let mut new_pairs: Vec<Pair> = Vec::new();
        let mut closed = 0u8;
        let walk = |start: usize, visited: &mut Vec<bool>| -> (usize, Vec<i32>) {
            let mut node = start;
            let mut came = usize::MAX;
            let mut arcs = Vec::new();
            visited[node] = true;
            loop {
                let step = adjacency[node].iter().copied().find(|&e| e != came);
                let e = match step {
                    Some(e) => e,
                    None => break,
                };
                if edges[e].arc != -3 {
                    arcs.push(edges[e].arc);
                }
                node = if edges[e].a == node { edges[e].b } else { edges[e].a };
                came = e;
                if visited[node] {
                    break; // closed the cycle
                }
                visited[node] = true;
                if adjacency[node].len() == 1 {
                    break;
                }
            }
            (node, arcs)
        };
        for start in 0..total {
            if visited[start] || adjacency[start].len() != 1 {
                continue;
            }
            let (end, arcs) = walk(start, &mut visited);
            let (p, q) = (label_of(start), label_of(end));
            assert!(p != q, "degenerate boundary arc");
            new_pairs.push((p.min(q), p.max(q)));
            for arc in arcs {
                if arc >= 0 { m_arc[arc as usize] = Target::New(p) } else { s_arc[(-1 - arc) as usize] = Target::New(p) }
            }
        }
        for start in 0..total {
            if visited[start] {
                continue;
            }
            let (_, arcs) = walk(start, &mut visited);
            for arc in arcs {
                if arc >= 0 { m_arc[arc as usize] = Target::Closed(closed) } else { s_arc[(-1 - arc) as usize] = Target::Closed(closed) }
            }
            closed += 1;
        }
        let matching = self.intern(new_pairs);
        let glued = Rc::new(Glued { matching, closed, m_arc, s_arc });
        self.glued.insert((m, smoothing), glued.clone());
        glued
    }

    fn transfer_plan(&mut self, a: MId, b: MId, i_src: u8, i_tgt: u8, on_boundary: &[bool], slots: [u32; 4]) -> Rc<TransferPlan> {
        if let Some(found) = self.transfer_plans.get(&(a, b, i_src, i_tgt)) {
            return found.clone();
        }
        self.stats.transfer_plans += 1;
        let gs = self.glue(a, i_src, on_boundary, slots);
        let gt = self.glue(b, i_tgt, on_boundary, slots);
        let mm = self.basis(a, b);
        let nn = self.basis(gs.matching, gt.matching);
        let saddle = i_src != i_tgt;
        let nf = mm.count;
        let ndiscs = nf + if saddle { 1 } else { 2 };
        let idisc = |j: usize| nf + if saddle { 0 } else { j };
        let mut arc_of_slot = [0usize; 4];
        for (j, &(s, t)) in SMOOTHINGS[i_src as usize].iter().enumerate() {
            arc_of_slot[s] = j;
            arc_of_slot[t] = j;
        }
        let mut dsu = Dsu::new(ndiscs);
        let mut unions: Vec<usize> = Vec::with_capacity(4);
        for j in 0..4 {
            let label = slots[j];
            if on_boundary[label as usize] {
                let x = mm.circle(label);
                dsu.union(x, idisc(arc_of_slot[j]));
                unions.push(x);
            } else if let Some(j0) = (0..j).find(|&x| slots[x] == label) {
                let x = idisc(arc_of_slot[j0]);
                dsu.union(x, idisc(arc_of_slot[j]));
                unions.push(x);
            }
        }
        let mut gluings = vec![0i32; ndiscs];
        for &x in &unions {
            gluings[dsu.find(x)] += 1;
        }
        let mut discs = vec![0i32; ndiscs];
        let mut input = vec![0u32; ndiscs];
        for d in 0..ndiscs {
            let r = dsu.find(d);
            discs[r] += 1;
            if d < nf {
                input[r] |= 1 << d;
            }
        }
        let mut boundary = vec![0u32; ndiscs];
        let mut closed_src = vec![usize::MAX; gs.closed as usize];
        let mut closed_tgt = vec![usize::MAX; gt.closed as usize];
        let ma = self.matchings[a as usize].clone();
        let mb = self.matchings[b as usize].clone();
        {
            let mut record = |disc: usize, target: Target, closed: &mut Vec<usize>, dsu: &mut Dsu| {
                let r = dsu.find(disc);
                match target {
                    Target::New(p) => boundary[r] |= 1 << nn.circle(p),
                    Target::Closed(i) => closed[i as usize] = r,
                }
            };
            for (t, &(p, _)) in ma.iter().enumerate() {
                record(mm.circle(p), gs.m_arc[t], &mut closed_src, &mut dsu);
            }
            for j in 0..2 {
                record(idisc(j), gs.s_arc[j], &mut closed_src, &mut dsu);
            }
            for (t, &(p, _)) in mb.iter().enumerate() {
                record(mm.circle(p), gt.m_arc[t], &mut closed_tgt, &mut dsu);
            }
            for j in 0..2 {
                record(idisc(j), gt.s_arc[j], &mut closed_tgt, &mut dsu);
            }
        }
        let roots: Vec<usize> = (0..ndiscs).filter(|&d| discs[d] > 0).collect();
        let mut plans = Vec::new();
        for ls in 0..(1u8 << gs.closed) {
            'labels: for lt in 0..(1u8 << gt.closed) {
                let mut chi: Vec<i32> = (0..ndiscs).map(|d| discs[d] - gluings[d]).collect();
                let mut extra = vec![0u8; ndiscs];
                for (t, &comp) in closed_src.iter().enumerate() {
                    chi[comp] += 1;
                    extra[comp] += (ls >> t) & 1; // label x on a source circle: dotted cup
                }
                for (t, &comp) in closed_tgt.iter().enumerate() {
                    chi[comp] += 1;
                    extra[comp] += 1 - ((lt >> t) & 1); // coefficient of 1 on a target circle: dotted cap
                }
                let mut comps = Vec::with_capacity(roots.len());
                for &r in &roots {
                    let twice_genus = 2 - chi[r] - boundary[r].count_ones() as i32;
                    assert!(twice_genus >= 0 && twice_genus % 2 == 0, "impossible surface component at a crossing");
                    if twice_genus > 0 || extra[r] >= 2 {
                        continue 'labels;
                    }
                    comps.push(Comp { left: input[r], right: 0, boundary: boundary[r], extra: extra[r] });
                }
                plans.push((ls, lt, comps));
            }
        }
        let plan = Rc::new(TransferPlan { circles_out: nn.count, plans });
        self.transfer_plans.insert((a, b, i_src, i_tgt), plan.clone());
        plan
    }

    fn crossing_entries(&mut self, a: MId, b: MId, f: &Morph, i_src: u8, i_tgt: u8, on_boundary: &[bool], slots: [u32; 4]) -> Rc<Vec<(u8, u8, Morph)>> {
        let key = (a, b, f.clone(), i_src, i_tgt);
        if let Some(found) = self.transferred.get(&key) {
            return found.clone();
        }
        let plan = self.transfer_plan(a, b, i_src, i_tgt, on_boundary, slots);
        let mut terms = std::mem::take(&mut self.scratch_f);
        f.monomials(&mut terms);
        let (mut work, mut next) = (Vec::with_capacity(8), Vec::with_capacity(8));
        let mut entries = Vec::new();
        for (ls, lt, comps) in &plan.plans {
            let mut value = Morph::zero(plan.circles_out);
            for &t in &terms {
                evaluate(comps, t, 0, &mut value, &mut work, &mut next);
            }
            if !value.is_zero() {
                entries.push((*ls, *lt, value));
            }
        }
        self.scratch_f = terms;
        let entries = Rc::new(entries);
        self.transferred.insert(key, entries.clone());
        entries
    }
}

struct Obj {
    matching: MId,
    h: u32,
    alive: bool,
}

#[derive(Clone)]
pub struct ScanOptions {
    pub minfill: bool,
    pub tail: usize,
    pub max_objects: Option<usize>,
    pub deadline: Option<Instant>,
    /// Set by the winner of a race; a scan that sees it stops with `ScanError::Cancelled`.
    pub cancel: Option<Arc<AtomicBool>>,
}

impl Default for ScanOptions {
    fn default() -> Self {
        ScanOptions { minfill: true, tail: 0, max_objects: None, deadline: None, cancel: None }
    }
}

#[allow(dead_code)]
pub struct RankResult {
    pub rank: u64,
    pub by_degree: BTreeMap<u32, u64>,
    pub stats: Stats,
    pub order: Vec<usize>,
}

pub enum ScanError {
    Limit(String),
    Cancelled,
}

struct Complex {
    alg: Algebra,
    objs: Vec<Obj>,
    out: Vec<FxMap<u32, Morph>>,
    inc: Vec<FxSet<u32>>,
    alive: usize,
    on_boundary: Vec<bool>,
    boundary_size: usize,
    options: ScanOptions,
}

impl Complex {
    fn set(&mut self, a: u32, b: u32, value: Morph) {
        if value.is_zero() {
            self.out[a as usize].remove(&b);
            self.inc[b as usize].remove(&a);
        } else {
            self.out[a as usize].insert(b, value);
            self.inc[b as usize].insert(a);
        }
    }

    fn check(&self) -> Result<(), ScanError> {
        if let Some(flag) = &self.options.cancel {
            if flag.load(Ordering::Relaxed) {
                return Err(ScanError::Cancelled);
            }
        }
        match self.options.deadline {
            Some(d) if Instant::now() > d => Err(ScanError::Limit("time budget exhausted".into())),
            _ => Ok(()),
        }
    }

    fn add_crossing(&mut self, slots: [u32; 4], reduce_now: bool) -> Result<(), ScanError> {
        self.check()?;
        let started = Instant::now();
        self.alg.clear_stage();
        let old_objs = std::mem::take(&mut self.objs);
        let old_out = std::mem::take(&mut self.out);
        self.inc.clear();
        let mut base: Vec<[u32; 2]> = vec![[u32::MAX; 2]; old_objs.len()];
        let mut new_objs: Vec<Obj> = Vec::with_capacity(2 * self.alive);
        for (o, obj) in old_objs.iter().enumerate() {
            if !obj.alive {
                continue;
            }
            for i in 0..2u8 {
                let g = self.alg.glue(obj.matching, i, &self.on_boundary, slots);
                base[o][i as usize] = new_objs.len() as u32;
                for _ in 0..(1u32 << g.closed) {
                    new_objs.push(Obj { matching: g.matching, h: obj.h + i as u32, alive: true });
                }
            }
            if let Some(limit) = self.options.max_objects {
                if new_objs.len() > limit {
                    return Err(ScanError::Limit(format!("more than {} objects", limit)));
                }
            }
        }
        let count = new_objs.len();
        self.objs = new_objs;
        self.out = (0..count).map(|_| FxMap::default()).collect();
        self.inc = (0..count).map(|_| FxSet::default()).collect();
        self.alive = count;
        for (o, obj) in old_objs.iter().enumerate() {
            if !obj.alive {
                continue;
            }
            if o & 1023 == 1023 {
                self.check()?;                 // one crossing can dominate the budget
            }
            let m = obj.matching;
            let circles = self.alg.basis(m, m).count;
            let one = Morph::one(circles);
            let entries = self.alg.crossing_entries(m, m, &one, 0, 1, &self.on_boundary, slots);
            for (ls, lt, value) in entries.iter() {
                self.set(base[o][0] + *ls as u32, base[o][1] + *lt as u32, value.clone());
            }
            for (&o2, f) in old_out[o].iter() {
                let m2 = old_objs[o2 as usize].matching;
                for i in 0..2u8 {
                    let entries = self.alg.crossing_entries(m, m2, f, i, i, &self.on_boundary, slots);
                    for (ls, lt, value) in entries.iter() {
                        self.set(base[o][i as usize] + *ls as u32, base[o2 as usize][i as usize] + *lt as u32, value.clone());
                    }
                }
            }
        }
        for &e in &slots {
            let e = e as usize;
            if self.on_boundary[e] { self.boundary_size -= 1 } else { self.boundary_size += 1 }
            self.on_boundary[e] = !self.on_boundary[e];
        }
        let stats = &mut self.alg.stats;
        stats.max_boundary = stats.max_boundary.max(self.boundary_size);
        stats.max_objects_before = stats.max_objects_before.max(count);
        stats.time_transfer += started.elapsed();
        if reduce_now {
            let started = Instant::now();
            self.eliminate()?;
            self.alg.stats.time_eliminate += started.elapsed();
            self.alg.stats.max_objects_after = self.alg.stats.max_objects_after.max(self.alive);
        }
        Ok(())
    }

    #[inline]
    fn invertible(&self, a: u32, b: u32) -> bool {
        match self.out[a as usize].get(&b) {
            Some(f) => f.is_unit() && self.objs[a as usize].matching == self.objs[b as usize].matching,
            None => false,
        }
    }

    #[inline]
    fn cost(&self, a: u32, b: u32) -> u32 {
        ((self.out[a as usize].len() - 1) * (self.inc[b as usize].len() - 1)) as u32
    }

    fn eliminate(&mut self) -> Result<(), ScanError> {
        let minfill = self.options.minfill;
        let mut heap: BinaryHeap<Reverse<(u32, u32, u32)>> = BinaryHeap::new();
        let mut stack: Vec<(u32, u32)> = Vec::new();
        for a in 0..self.objs.len() as u32 {
            let targets: Vec<u32> = self.out[a as usize].keys().copied().collect();
            for b in targets {
                if self.invertible(a, b) {
                    if minfill { heap.push(Reverse((self.cost(a, b), a, b))) } else { stack.push((a, b)) }
                }
            }
        }
        let mut counter = 0u32;
        loop {
            let (b, c) = if minfill {
                match heap.pop() {
                    Some(Reverse((cost, b, c))) => {
                        if !self.objs[b as usize].alive || !self.objs[c as usize].alive || !self.invertible(b, c) {
                            continue;
                        }
                        let now = self.cost(b, c);
                        if now != cost {
                            heap.push(Reverse((now, b, c)));
                            continue;
                        }
                        (b, c)
                    }
                    None => break,
                }
            } else {
                match stack.pop() {
                    Some((b, c)) => {
                        if !self.objs[b as usize].alive || !self.objs[c as usize].alive || !self.invertible(b, c) {
                            continue;
                        }
                        (b, c)
                    }
                    None => break,
                }
            };
            counter += 1;
            if counter & 255 == 0 {
                self.check()?;
            }
            let m = self.objs[b as usize].matching;
            let phi_inv = self.out[b as usize][&c].clone(); // units are involutions over F2
            let ins: Vec<(u32, Morph)> = self.inc[c as usize].iter().filter(|&&a| a != b).map(|&a| (a, self.out[a as usize][&c].clone())).collect();
            let outs: Vec<(u32, Morph)> = self.out[b as usize].iter().filter(|(&f, _)| f != c).map(|(&f, v)| (f, v.clone())).collect();
            for (a, delta) in &ins {
                let ma = self.objs[*a as usize].matching;
                let half = self.alg.compose(delta, &phi_inv, ma, m, m);
                if half.is_zero() {
                    continue;
                }
                for (f, gamma) in &outs {
                    let mf = self.objs[*f as usize].matching;
                    let term = self.alg.compose(&half, gamma, ma, m, mf);
                    if term.is_zero() {
                        continue;
                    }
                    let current = match self.out[*a as usize].get(f) {
                        Some(v) => {
                            let mut c = v.clone();
                            c.xor_assign(&term);
                            c
                        }
                        None => term,
                    };
                    let nonzero = !current.is_zero();
                    self.set(*a, *f, current);
                    if nonzero && self.invertible(*a, *f) {
                        if minfill { heap.push(Reverse((self.cost(*a, *f), *a, *f))) } else { stack.push((*a, *f)) }
                    }
                }
            }
            for x in [b, c] {
                let targets: Vec<u32> = self.out[x as usize].keys().copied().collect();
                for y in targets {
                    self.inc[y as usize].remove(&x);
                }
                self.out[x as usize] = FxMap::default();
                let sources: Vec<u32> = self.inc[x as usize].iter().copied().collect();
                for y in sources {
                    self.out[y as usize].remove(&x);
                }
                self.inc[x as usize] = FxSet::default();
                self.objs[x as usize].alive = false;
            }
            self.alive -= 2;
            self.alg.stats.eliminations += 1;
        }
        Ok(())
    }

    /// Homology dimensions of the closed complex by F2 linear algebra.
    fn linear_ranks(&mut self) -> BTreeMap<u32, u64> {
        let started = Instant::now();
        let mut by_degree: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        for (i, o) in self.objs.iter().enumerate() {
            if o.alive {
                by_degree.entry(o.h).or_default().push(i as u32);
            }
        }
        let mut rank: BTreeMap<u32, u64> = BTreeMap::new();
        for (&h, sources) in &by_degree {
            let empty = Vec::new();
            let targets = by_degree.get(&(h + 1)).unwrap_or(&empty);
            let index: FxMap<u32, usize> = targets.iter().enumerate().map(|(k, &t)| (t, k)).collect();
            let words = (targets.len() + 63) / 64;
            let mut pivots: FxMap<usize, Vec<u64>> = FxMap::default();
            for &a in sources {
                let mut column = vec![0u64; words];
                for (b, v) in self.out[a as usize].iter() {
                    if !v.is_zero() {
                        let k = index[b];
                        column[k / 64] ^= 1 << (k % 64);
                    }
                }
                loop {
                    let top = match column.iter().rposition(|&w| w != 0) {
                        Some(w) => w * 64 + 63 - column[w].leading_zeros() as usize,
                        None => break,
                    };
                    match pivots.get(&top) {
                        Some(p) => column.iter_mut().zip(p.iter()).for_each(|(x, y)| *x ^= *y),
                        None => {
                            pivots.insert(top, column);
                            break;
                        }
                    }
                }
            }
            rank.insert(h, pivots.len() as u64);
        }
        let mut result = BTreeMap::new();
        for (&h, sources) in &by_degree {
            let below = if h == 0 { 0 } else { *rank.get(&(h - 1)).unwrap_or(&0) };
            let dim = sources.len() as u64 - rank[&h] - below;
            if dim > 0 {
                result.insert(h, dim);
            }
        }
        self.alg.stats.time_linear += started.elapsed();
        result
    }
}

/// Unreduced F2 Khovanov ranks of a validated knot PD code, by cube degree.
pub fn khovanov_rank(pd: &[[u32; 4]], order: Vec<usize>, options: ScanOptions) -> Result<RankResult, ScanError> {
    let n = pd.len();
    if n == 0 {
        let mut by_degree = BTreeMap::new();
        by_degree.insert(0, 2);
        return Ok(RankResult { rank: 2, by_degree, stats: Stats::default(), order });
    }
    let tail = options.tail;
    let mut alg = Algebra::new();
    let empty = alg.intern(Vec::new());
    let mut complex = Complex {
        alg,
        objs: vec![Obj { matching: empty, h: 0, alive: true }],
        out: vec![FxMap::default()],
        inc: vec![FxSet::default()],
        alive: 1,
        on_boundary: vec![false; 2 * n],
        boundary_size: 0,
        options,
    };
    for (position, &index) in order.iter().enumerate() {
        complex.add_crossing(pd[index], position + tail < n)?;
    }
    let by_degree = if tail > 0 {
        complex.linear_ranks()
    } else {
        let mut counts = BTreeMap::new();
        for o in complex.objs.iter().filter(|o| o.alive) {
            *counts.entry(o.h).or_insert(0u64) += 1;
        }
        assert!(complex.out.iter().all(|m| m.is_empty()), "minimal closed complex has a nonzero differential");
        counts
    };
    let rank = by_degree.values().sum();
    let mut stats = complex.alg.stats.clone();
    stats.matchings = complex.alg.matchings.len();
    Ok(RankResult { rank, by_degree, stats, order })
}


/// Race several scan orders on separate threads; the first to finish wins and cancels the rest.
/// Rank and ranks by degree do not depend on the order, so the result is the same whoever wins;
/// `order` and `stats` are the winner's.  A competitor that hits a resource limit does not end
/// the race (limits such as `max_objects` depend on the order); the limit is reported only if
/// every competitor hits one.  Competitors other than the first start after `head_start`.
/// Returns the result and the index of the winning order.
pub fn race(pd: &[[u32; 4]], orders: Vec<Vec<usize>>, options: ScanOptions, head_start: Duration) -> (Result<RankResult, ScanError>, usize) {
    if orders.len() == 1 {
        return (khovanov_rank(pd, orders.into_iter().next().unwrap(), options), 0);
    }
    let cancel = Arc::new(AtomicBool::new(false));
    let (sender, receiver) = std::sync::mpsc::channel();
    let competitors = orders.len();
    // The late starters wait on a channel, not on a sleep: when the first order finishes, its end of
    // the channel is dropped and they wake at once.  (Polling with sleep(1 ms) cost up to a timer
    // tick, about 15 ms on Windows, before the scope could return: 4 to 13% on scans under 100 ms.)
    let (wake, waiters): (Vec<_>, Vec<_>) = (1..competitors).map(|_| std::sync::mpsc::channel::<()>()).unzip();
    let mut wake = Some(wake);
    let mut waiters = waiters.into_iter();
    std::thread::scope(|scope| {
        for (k, order) in orders.into_iter().enumerate() {
            let sender = sender.clone();
            let mut mine = options.clone();
            mine.cancel = Some(cancel.clone());
            let cancel = cancel.clone();
            let held = if k == 0 { wake.take() } else { None };
            let waiter = if k == 0 { None } else { waiters.next() };
            scope.spawn(move || {
                // The first order gets a head start: most scans finish within it and then pay nothing
                // for the race, while a late start costs a long scan next to nothing.
                if let Some(waiter) = waiter {
                    let _ = waiter.recv_timeout(head_start);        // a timeout, or the first order is done
                    if cancel.load(Ordering::Relaxed) {
                        let _ = sender.send((k, Err(ScanError::Cancelled)));
                        return;
                    }
                }
                let result = khovanov_rank(pd, order, mine);
                if result.is_ok() {
                    cancel.store(true, Ordering::Relaxed);
                }
                drop(held);                                          // wakes the late starters
                let _ = sender.send((k, result));
            });
        }
        drop(sender);
        let mut limit = None;
        for _ in 0..competitors {
            match receiver.recv() {
                Ok((k, Ok(result))) => return (Ok(result), k),
                Ok((k, Err(ScanError::Limit(reason)))) => limit = Some((ScanError::Limit(reason), k)),
                Ok((_, Err(ScanError::Cancelled))) | Err(_) => {}
            }
        }
        let (error, k) = limit.unwrap_or((ScanError::Cancelled, 0));
        (Err(error), k)
    })
}
