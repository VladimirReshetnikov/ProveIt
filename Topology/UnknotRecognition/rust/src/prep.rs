//! Polynomial-time preprocessing: incremental Reidemeister I/II reduction, the
//! linear descending-diagram test, greedy scan orders and visible connected-sum
//! factorization.

use crate::diagram::{rot, Diagram};
use crate::util::FxMap;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

// ---------------------------------------------------------------------------
// Reidemeister I/II
// ---------------------------------------------------------------------------

struct Darts {
    alpha: Vec<u32>,
    alive: Vec<bool>,
    remaining: usize,
}

enum Move {
    R1(u32),
    R2(u32, u32),
}

impl Darts {
    fn next(&self, d: u32) -> u32 {
        rot(self.alpha[d as usize])
    }

    fn move_at(&self, d: u32) -> Option<Move> {
        if !self.alive[(d / 4) as usize] {
            return None;
        }
        let e = self.next(d);
        if e == d {
            return Some(Move::R1(d));
        }
        if e / 4 != d / 4 && self.next(e) == d && d % 2 == self.alpha[d as usize] % 2 && e % 2 == self.alpha[e as usize] % 2 {
            return Some(Move::R2(d, e));
        }
        None
    }

    /// `through` is a fixed-point-free involution on the darts where strands leave the removed region.
    fn splice(&mut self, through: &[(u32, u32)], touched: &mut Vec<u32>) {
        let partner = |x: u32| through.iter().find_map(|&(a, b)| if a == x { Some(b) } else if b == x { Some(a) } else { None });
        let mut done: Vec<u32> = Vec::with_capacity(4);
        for &(a, b) in through {
            for x in [a, b] {
                let outer = self.alpha[x as usize];
                if partner(outer).is_some() || done.contains(&outer) {
                    continue;
                }
                let mut y = self.alpha[partner(x).unwrap() as usize];
                while let Some(p) = partner(y) {
                    y = self.alpha[p as usize];
                }
                self.alpha[outer as usize] = y;
                self.alpha[y as usize] = outer;
                done.push(outer);
                done.push(y);
                touched.push(outer);
                touched.push(y);
            }
        }
    }

    fn apply(&mut self, mv: &Move, touched: &mut Vec<u32>) -> usize {
        let (through, removed): (Vec<(u32, u32)>, Vec<u32>) = match *mv {
            Move::R1(d) => {
                let (base, j) = (d & !3, d & 3);
                (vec![(base | ((j + 1) & 3), base | ((j + 2) & 3))], vec![d / 4])
            }
            Move::R2(d, e) => {
                let (a, j, b, k) = (d & !3, d & 3, e & !3, e & 3);
                (vec![(a | ((j + 2) & 3), b | ((k + 1) & 3)), (a | ((j + 1) & 3), b | ((k + 2) & 3))], vec![d / 4, e / 4])
            }
        };
        for &c in &removed {
            self.alive[c as usize] = false;
        }
        self.remaining -= removed.len();
        if self.remaining > 0 {
            self.splice(&through, touched);
        }
        removed.len()
    }

    // ----- Reidemeister III ---------------------------------------------------

    /// The darts of a triangular face through `d` that admits an R3 move.  Side k is the edge
    /// (d_k, alpha[d_k]); a slot is on the over-strand iff it is odd; the triangle can be
    /// inverted iff some side is over at both ends.
    fn triangle_at(&self, d: u32) -> Option<[u32; 3]> {
        if !self.alive[(d / 4) as usize] {
            return None;
        }
        let e = self.next(d);
        let f = self.next(e);
        if self.next(f) != d || d / 4 == e / 4 || e / 4 == f / 4 || d / 4 == f / 4 {
            return None;
        }
        let t = [d, e, f];
        if t.iter().any(|&x| x % 2 == 1 && self.alpha[x as usize] % 2 == 1) { Some(t) } else { None }
    }

    /// Necessary for the inverted triangle to create a I/II move: a face across some side has
    /// at most three edges (inverting takes one edge from each of those faces).
    fn r3_can_help(&self, t: &[u32; 3]) -> bool {
        t.iter().any(|&d| {
            let start = self.alpha[d as usize];
            let (mut x, mut size) = (self.next(start), 1);
            while x != start && size < 4 {
                x = self.next(x);
                size += 1;
            }
            x == start && size <= 3
        })
    }

    /// Invert the triangle: every strand meets the other two in the opposite order, each crossing
    /// keeps its slots and the direction of both strands, hence its sign.  An involution.
    /// Returns false, changing nothing, in a degenerate configuration.
    fn apply_r3(&mut self, t: &[u32; 3]) -> bool {
        let inner = [self.alpha[t[0] as usize], self.alpha[t[1] as usize], self.alpha[t[2] as usize]];
        let mut moved = [(0u32, 0u32); 6];
        for k in 0..3 {
            moved[2 * k] = (t[k] ^ 2, inner[k]);          // the strand now enters at i_k ...
            moved[2 * k + 1] = (inner[k] ^ 2, t[k]);      // ... and leaves at d_k
        }
        for a in 0..6 {
            for b in a + 1..6 {
                if moved[a].0 == moved[b].0 {
                    return false;
                }
            }
        }
        let mut links = [(0u32, 0u32); 9];
        for (k, &(x, new_x)) in moved.iter().enumerate() {
            let y = self.alpha[x as usize];
            let new_y = moved.iter().find(|m| m.0 == y).map_or(y, |m| m.1);
            if new_y == new_x {
                return false;
            }
            links[k] = (new_x, new_y);
        }
        for k in 0..3 {
            links[6 + k] = (inner[k] ^ 2, t[k] ^ 2);      // the sides of the inverted triangle
        }
        for &(x, y) in &links {
            self.alpha[x as usize] = y;
            self.alpha[y as usize] = x;
        }
        true
    }

    fn rebuild(&self) -> Diagram {
        let mut label: FxMap<u32, i64> = FxMap::default();
        let mut rows = Vec::with_capacity(self.remaining);
        for (i, &alive) in self.alive.iter().enumerate() {
            if !alive {
                continue;
            }
            let mut row = [0i64; 4];
            for j in 0..4 {
                let d = (4 * i + j) as u32;
                let key = d.min(self.alpha[d as usize]);
                let next = label.len() as i64;
                row[j] = *label.entry(key).or_insert(next);
            }
            rows.push(row);
        }
        Diagram::from_pd(&rows).expect("Reidemeister reduction preserves validity")
    }
}

/// Crossing-decreasing R1/R2 moves until none applies; returns the reduced diagram and the move count.
pub fn simplify(diagram: &Diagram) -> (Diagram, usize) {
    let n = diagram.crossings();
    if n == 0 {
        return (diagram.clone(), 0);
    }
    let mut state = Darts { alpha: diagram.alpha(), alive: vec![true; n], remaining: n };
    let mut stack: Vec<u32> = (0..4 * n as u32).rev().collect();
    let mut moves = 0;
    let mut touched = Vec::with_capacity(4);
    while let Some(d) = stack.pop() {
        if state.remaining == 0 {
            break;
        }
        if let Some(mv) = state.move_at(d) {
            touched.clear();
            state.apply(&mv, &mut touched);
            moves += 1;
            stack.extend_from_slice(&touched);
        }
    }
    (state.rebuild(), moves)
}

fn around(t: &[u32; 3]) -> Vec<u32> {
    t.iter().flat_map(|&x| (0..4).map(move |j| (x & !3) | j)).collect()
}

/// Depth-first search for at most `depth` R3 moves after which a I/II move exists.  On success the
/// moves stay applied and `found` holds the darts to look at; otherwise the structure is restored.
/// After the first move only triangles next to it are tried, never the inverse of the last move.
fn unlock(state: &mut Darts, depth: usize, darts: &[u32], undo_of: Option<[u32; 3]>, trials: &mut usize, budget: usize,
          kept: &mut usize, found: &mut Vec<u32>) -> bool {
    let mut seen: Vec<u32> = Vec::new();
    for &d in darts {
        if *trials >= budget {
            return false;
        }
        let Some(t) = state.triangle_at(d) else { continue };
        let low = *t.iter().min().unwrap();
        if seen.contains(&low) {
            continue;
        }
        seen.push(low);
        if let Some(u) = undo_of {
            if t.iter().all(|x| u.contains(x)) {
                continue;
            }
        }
        if depth == 1 && !state.r3_can_help(&t) {
            continue;
        }
        if !state.apply_r3(&t) {
            continue;
        }
        *trials += 1;
        let near = around(&t);
        if near.iter().any(|&x| state.move_at(x).is_some()) {
            *kept += 1;
            found.extend_from_slice(&near);
            return true;
        }
        if depth > 1 {
            let mut crossings: Vec<u32> = near.iter().flat_map(|&x| [x / 4, state.alpha[x as usize] / 4]).collect();
            crossings.sort_unstable();
            crossings.dedup();
            let next: Vec<u32> = crossings.iter().flat_map(|&c| (0..4).map(move |j| 4 * c + j)).collect();
            if unlock(state, depth - 1, &next, Some([t[0] ^ 2, t[1] ^ 2, t[2] ^ 2]), trials, budget, kept, found) {
                *kept += 1;
                found.extend_from_slice(&near);
                return true;
            }
        }
        let back = state.triangle_at(t[0] ^ 2).expect("the inverted triangle is a triangle");
        state.apply_r3(&back);
    }
    false
}

/// I/II reduction helped by Reidemeister III: when no I/II move is left, sequences of at most
/// `depth` R3 moves are tried, shortest first, and kept if they create a I/II move.  Deeper
/// sequences are tried only while fewer than `budget` trial moves per crossing were made (a
/// diagram full of useless triangles makes depth 4 cost a hundred times depth 1, while useful
/// sequences are found early).  Returns the diagram, the I/II moves and the R3 moves kept.
pub fn simplify_r3(diagram: &Diagram, depth: usize, budget: usize) -> (Diagram, usize, usize) {
    let n = diagram.crossings();
    if n == 0 {
        return (diagram.clone(), 0, 0);
    }
    let mut state = Darts { alpha: diagram.alpha(), alive: vec![true; n], remaining: n };
    let mut stack: Vec<u32> = (0..4 * n as u32).rev().collect();
    let all: Vec<u32> = (0..4 * n as u32).collect();
    let (mut moves, mut kept, mut trials) = (0, 0, 0);
    let mut touched = Vec::with_capacity(4);
    loop {
        while let Some(d) = stack.pop() {
            if state.remaining == 0 {
                break;
            }
            if let Some(mv) = state.move_at(d) {
                touched.clear();
                state.apply(&mv, &mut touched);
                moves += 1;
                stack.extend_from_slice(&touched);
            }
        }
        if state.remaining < 3 {
            break;
        }
        let mut found = Vec::new();
        if !(1..=depth).any(|k| unlock(&mut state, k, &all, None, &mut trials, budget * n, &mut kept, &mut found)) {
            break;
        }
        stack = found;
    }
    (state.rebuild(), moves, kept)
}

// ---------------------------------------------------------------------------
// descending diagrams
// ---------------------------------------------------------------------------

/// True when some basepoint and direction meet every crossing first on its over-strand.
pub fn is_descending(diagram: &Diagram) -> bool {
    let n = diagram.crossings();
    if n == 0 {
        return true;
    }
    let forward = diagram.traversal();
    let length = forward.len();
    let backward: Vec<u32> = forward.iter().rev().map(|&d| d ^ 2).collect();
    for walk in [&forward, &backward] {
        let mut over = vec![0usize; n];
        let mut under = vec![0usize; n];
        for (k, &dart) in walk.iter().enumerate() {
            if dart % 2 == 1 { over[(dart / 4) as usize] = k } else { under[(dart / 4) as usize] = k }
        }
        let mut diff = vec![0i32; length + 1];
        for c in 0..n {
            let (left, right) = ((over[c] + 1) % length, under[c]);
            if left <= right {
                diff[left] += 1;
                diff[right + 1] -= 1;
            } else {
                diff[left] += 1;
                diff[length] -= 1;
                diff[0] += 1;
                diff[right + 1] -= 1;
            }
        }
        let mut bad = 0;
        for k in 0..length {
            bad += diff[k];
            if bad == 0 {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// scan orders
// ---------------------------------------------------------------------------

pub fn order_profile(pd: &[[u32; 4]], order: &[usize]) -> (usize, usize) {
    let mut on = vec![false; 2 * pd.len()];
    let (mut size, mut worst, mut total) = (0usize, 0usize, 0usize);
    for &i in order {
        for &e in &pd[i] {
            let e = e as usize;
            if on[e] { size -= 1 } else { size += 1 }
            on[e] = !on[e];
        }
        worst = worst.max(size);
        total += size;
    }
    (worst, total)
}

/// How the greedy rule breaks ties between crossings with equally many edges into the processed
/// region.  The rules are incomparable: on 81 test diagrams each is better on about as many
/// inputs as it is worse, with per-diagram work ratios from 0.01 to 28.  That is what a race uses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ties {
    /// smallest crossing index (the rule of the Python package)
    Index,
    /// the crossing that has been waiting longest since it first touched the processed region
    Oldest,
    /// the crossing touched most recently
    Recent,
}

fn greedy(neighbours: &[Vec<u32>], loops: &[u32], start: usize, ties: Ties) -> Vec<usize> {
    let n = neighbours.len();
    let mut active = vec![true; n];
    let mut shared = vec![0u32; n];
    let mut tie = vec![0u32; n];
    // max shared, then max loops, then the tie rule, then min index
    let mut heap: BinaryHeap<(u32, u32, u32, Reverse<usize>)> = (0..n).map(|i| (0, loops[i], 0, Reverse(i))).collect();
    let mut order = Vec::with_capacity(n);
    let mut current = start;
    let mut clock = 0u32;
    while order.len() < n {
        if !order.is_empty() {
            loop {
                let (s, _, t, Reverse(i)) = heap.pop().expect("heap exhausted");
                if active[i] && s == shared[i] && t == tie[i] {
                    current = i;
                    break;
                }
            }
        }
        order.push(current);
        active[current] = false;
        clock += 1;
        for &other in &neighbours[current] {
            let o = other as usize;
            if active[o] {
                shared[o] += 1;
                match ties {
                    Ties::Index => {}
                    Ties::Oldest => {
                        if tie[o] == 0 {
                            tie[o] = u32::MAX - clock;      // earlier first touch = larger key
                        }
                    }
                    Ties::Recent => tie[o] = clock,
                }
                heap.push((shared[o], loops[o], tie[o], Reverse(o)));
            }
        }
    }
    order
}

fn graph(pd: &[[u32; 4]]) -> (Vec<Vec<u32>>, Vec<u32>) {
    let n = pd.len();
    let mut owner = vec![u32::MAX; 2 * n];
    let mut neighbours: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut loops = vec![0u32; n];
    for (i, row) in pd.iter().enumerate() {
        for &e in row {
            let e = e as usize;
            if owner[e] == u32::MAX {
                owner[e] = i as u32;
            } else if owner[e] as usize == i {
                loops[i] += 1;
            } else {
                neighbours[i].push(owner[e]);
                neighbours[owner[e] as usize].push(i as u32);
            }
        }
    }
    (neighbours, loops)
}

/// Greedy small-boundary orders from up to `tries` starts; the best boundary profile wins.
pub fn best_scan_order(pd: &[[u32; 4]], tries: usize) -> Vec<usize> {
    best_scan_order_with(pd, tries, Ties::Index)
}

pub fn best_scan_order_with(pd: &[[u32; 4]], tries: usize, ties: Ties) -> Vec<usize> {
    let n = pd.len();
    if n == 0 {
        return Vec::new();
    }
    let (neighbours, loops) = graph(pd);
    let step = if tries >= n { 1 } else { (n / tries).max(1) };
    let mut best: Option<(Vec<usize>, (usize, usize))> = None;
    let mut start = 0;
    while start < n {
        let order = greedy(&neighbours, &loops, start, ties);
        let profile = order_profile(pd, &order);
        if best.as_ref().map_or(true, |(_, p)| profile < *p) {
            best = Some((order, profile));
        }
        start += step;
    }
    best.unwrap().0
}

/// Up to `count` distinct orders for a race: the three tie rules, in the order in which they did
/// best in the experiments (index, oldest, recent).  The first is always the default order.
pub fn race_orders(pd: &[[u32; 4]], tries: usize, count: usize) -> Vec<(Ties, Vec<usize>)> {
    let mut orders: Vec<(Ties, Vec<usize>)> = Vec::new();
    for ties in [Ties::Index, Ties::Oldest, Ties::Recent] {
        if orders.len() >= count.max(1) {
            break;
        }
        let order = best_scan_order_with(pd, tries, ties);
        if !orders.iter().any(|(_, o)| *o == order) {
            orders.push((ties, order));
        }
    }
    orders
}

// ---------------------------------------------------------------------------
// visible connected sums
// ---------------------------------------------------------------------------

fn split_once(diagram: &Diagram) -> Option<(Diagram, Diagram)> {
    let n = diagram.crossings();
    if n < 2 {
        return None;
    }
    let alpha = diagram.alpha();
    let mut face_of = vec![0u32; 4 * n];
    for (index, face) in diagram.faces().iter().enumerate() {
        for &d in face {
            face_of[d as usize] = index as u32;
        }
    }
    let mut by_faces: FxMap<(u32, u32), Vec<u32>> = FxMap::default();
    for d in 0..4 * n as u32 {
        let o = alpha[d as usize];
        if d < o {
            let (a, b) = (face_of[d as usize], face_of[o as usize]);
            if a != b {
                by_faces.entry((a.min(b), a.max(b))).or_default().push(diagram.pd[(d / 4) as usize][(d % 4) as usize]);
            }
        }
    }
    let walk = diagram.traversal();
    let mut position = vec![0usize; 2 * n];
    for (k, &d) in walk.iter().enumerate() {
        position[diagram.pd[(d / 4) as usize][(d % 4) as usize] as usize] = k;
    }
    let mut best: Option<(usize, usize, usize)> = None;
    let mut groups: Vec<&Vec<u32>> = by_faces.values().filter(|g| g.len() >= 2).collect();
    groups.sort();
    for group in groups {
        let mut stops: Vec<usize> = group.iter().map(|&e| position[e as usize]).collect();
        stops.sort_unstable();
        for w in 0..stops.len() {
            let x = stops[w];
            let y = if w + 1 < stops.len() { stops[w + 1] } else { stops[0] + 2 * n };
            let length = y - x;
            let balance = length.min(2 * n - length);
            if best.map_or(true, |(b, _, _)| balance > b) {
                best = Some((balance, x, y % (2 * n)));
            }
        }
    }
    let (_, x, y) = best?;
    let mut inside = vec![false; n];
    let mut k = x;
    while k != y {
        inside[(walk[k] / 4) as usize] = true;
        k = (k + 1) % (2 * n);
    }
    let edge = |k: usize| diagram.pd[(walk[k] / 4) as usize][(walk[k] % 4) as usize];
    let (ex, ey) = (edge(x), edge(y));
    let mut pieces = Vec::with_capacity(2);
    for side in [true, false] {
        let rows: Vec<[i64; 4]> = diagram
            .pd
            .iter()
            .enumerate()
            .filter(|(i, _)| inside[*i] == side)
            .map(|(_, r)| {
                let f = |e: u32| if e == ey { ex as i64 } else { e as i64 };
                [f(r[0]), f(r[1]), f(r[2]), f(r[3])]
            })
            .collect();
        if rows.is_empty() {
            return None;
        }
        pieces.push(Diagram::from_pd(&rows).ok()?);
    }
    let right = pieces.pop().unwrap();
    let left = pieces.pop().unwrap();
    Some((left, right))
}

/// The summands exposed by repeatedly cutting along two-edge cuts of the projection.
pub fn visible_factors(diagram: &Diagram) -> Vec<Diagram> {
    let mut pending = vec![diagram.clone()];
    let mut factors = Vec::new();
    while let Some(current) = pending.pop() {
        match split_once(&current) {
            None => factors.push(current),
            Some((left, right)) => {
                pending.push(right);
                pending.push(left);
            }
        }
    }
    factors
}
