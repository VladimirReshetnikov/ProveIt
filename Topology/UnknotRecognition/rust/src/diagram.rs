//! Validated classical one-component knot diagrams (PD codes), with converters
//! from braid closures and rectangular (grid) diagrams.
//!
//! A crossing is `[a, b, c, d]` counterclockwise with the under-strand `a-c`.
//! Dart `4 i + j` is slot `j` of crossing `i`; `alpha` pairs the two darts of an
//! edge and the face walk is `d -> rot(alpha[d])`.

use crate::json::Json;
use crate::util::Dsu;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagram {
    pub pd: Vec<[u32; 4]>,
}

#[inline]
pub fn rot(d: u32) -> u32 {
    (d & !3) | ((d + 1) & 3)
}

impl Diagram {
    pub fn crossings(&self) -> usize {
        self.pd.len()
    }

    pub fn from_pd(rows: &[[i64; 4]]) -> Result<Diagram, String> {
        if rows.is_empty() {
            return Ok(Diagram { pd: Vec::new() });
        }
        let mut counts: HashMap<i64, u32> = HashMap::new();
        for row in rows {
            for &x in row {
                *counts.entry(x).or_insert(0) += 1;
            }
        }
        if counts.values().any(|&c| c != 2) {
            return Err("every edge label must occur exactly twice".into());
        }
        let mut labels: Vec<i64> = counts.keys().copied().collect();
        labels.sort_unstable();
        let relabel: HashMap<i64, u32> = labels.iter().enumerate().map(|(i, &l)| (l, i as u32)).collect();
        let pd: Vec<[u32; 4]> = rows.iter().map(|r| [relabel[&r[0]], relabel[&r[1]], relabel[&r[2]], relabel[&r[3]]]).collect();
        let d = Diagram { pd };
        let n = d.pd.len();
        let alpha = d.alpha();
        let mut strands = Dsu::new(4 * n);
        for dart in 0..4 * n {
            strands.union(dart, alpha[dart] as usize);
        }
        for i in 0..n {
            strands.union(4 * i, 4 * i + 2);
            strands.union(4 * i + 1, 4 * i + 3);
        }
        let root = strands.find(0);
        if (0..4 * n).any(|x| strands.find(x) != root) {
            return Err("the diagram must have exactly one component".into());
        }
        if d.faces().len() != n + 2 {
            return Err("the rotation system is not spherical (virtual diagram)".into());
        }
        Ok(d)
    }

    pub fn from_braid(strands: usize, word: &[i64]) -> Result<Diagram, String> {
        if strands < 1 {
            return Err("strands must be positive".into());
        }
        if word.iter().any(|&g| g == 0 || g.unsigned_abs() as usize >= strands) {
            return Err("braid generators must satisfy 1 <= |g| < strands".into());
        }
        if strands > word.len() + 1 {
            return Err("too few crossings for a one-component closure".into());
        }
        let mut perm: Vec<usize> = (0..strands).collect();
        for &g in word {
            let i = g.unsigned_abs() as usize - 1;
            perm.swap(i, i + 1);
        }
        let mut seen = vec![false; strands];
        let mut x = 0;
        let mut length = 0;
        while !seen[x] {
            seen[x] = true;
            x = perm[x];
            length += 1;
        }
        if length != strands {
            return Err("the braid closure is a link, not a knot".into());
        }
        let mut current: Vec<usize> = (0..strands).collect();
        let mut next = strands;
        let mut rows: Vec<[usize; 4]> = Vec::with_capacity(word.len());
        for &g in word {
            let i = g.unsigned_abs() as usize - 1;
            let (left, right) = (current[i], current[i + 1]);
            let (ol, or) = (next, next + 1);
            next += 2;
            rows.push(if g > 0 { [right, left, ol, or] } else { [left, ol, or, right] });
            current[i] = ol;
            current[i + 1] = or;
        }
        let mut closure = Dsu::new(next);
        for (top, &bottom) in current.iter().enumerate() {
            closure.union(top, bottom);
        }
        let rows: Vec<[i64; 4]> = rows
            .iter()
            .map(|r| [closure.find(r[0]) as i64, closure.find(r[1]) as i64, closure.find(r[2]) as i64, closure.find(r[3]) as i64])
            .collect();
        Diagram::from_pd(&rows)
    }

    /// Rectangular diagram: two marked columns per row, rows bottom to top, verticals over.
    pub fn from_grid(input: &[[i64; 2]]) -> Result<Diagram, String> {
        let n = input.len();
        let mut rows: Vec<[usize; 2]> = Vec::with_capacity(n);
        for r in input {
            let (a, b) = (r[0].min(r[1]), r[0].max(r[1]));
            if n < 2 || a < 0 || b as usize >= n || a == b {
                return Err("a grid needs two distinct column indices in each row".into());
            }
            rows.push([a as usize, b as usize]);
        }
        let mut cols: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (r, row) in rows.iter().enumerate() {
            cols[row[0]].push(r);
            cols[row[1]].push(r);
        }
        if cols.iter().any(|c| c.len() != 2) {
            return Err("every column must contain exactly two corners".into());
        }
        let mut ids: HashMap<(usize, usize), usize> = HashMap::new();
        let mut events: Vec<(usize, bool, i64)> = Vec::new();
        let (mut r, mut c) = (0usize, rows[0][0]);
        let start = (r, c);
        let mut visited = 0;
        loop {
            let d = if c == rows[r][0] { rows[r][1] } else { rows[r][0] };
            let dx: i64 = if d > c { 1 } else { -1 };
            let mut col = c as i64 + dx;
            while col != d as i64 {
                let (lo, hi) = (cols[col as usize][0], cols[col as usize][1]);
                if lo < r && r < hi {
                    let next_id = ids.len();
                    let id = *ids.entry((r, col as usize)).or_insert(next_id);
                    events.push((id, false, dx));
                }
                col += dx;
            }
            c = d;
            let s = if r == cols[c][0] { cols[c][1] } else { cols[c][0] };
            let dy: i64 = if s > r { 1 } else { -1 };
            let mut row = r as i64 + dy;
            while row != s as i64 {
                let (a2, b2) = (rows[row as usize][0], rows[row as usize][1]);
                if a2 < c && c < b2 {
                    let next_id = ids.len();
                    let id = *ids.entry((row as usize, c)).or_insert(next_id);
                    events.push((id, true, dy));
                }
                row += dy;
            }
            r = s;
            visited += 1;
            if (r, c) == start {
                break;
            }
            if visited > n {
                return Err("the grid has more than one component".into());
            }
        }
        if visited != n {
            return Err("the grid has more than one component".into());
        }
        let m = events.len();
        if m == 0 {
            return Ok(Diagram { pd: Vec::new() });
        }
        let mut under = vec![(0usize, 0usize, 0i64); ids.len()];
        let mut over = under.clone();
        for (k, &(id, is_over, dir)) in events.iter().enumerate() {
            let entry = ((k + m - 1) % m, k, dir);
            if is_over { over[id] = entry } else { under[id] = entry }
        }
        let mut pd = Vec::with_capacity(ids.len());
        for id in 0..ids.len() {
            let (u_in, u_out, dx) = under[id];
            let (o_in, o_out, dy) = over[id];
            let (south, north) = if dy == 1 { (o_in, o_out) } else { (o_out, o_in) };
            let row = if dx == 1 { [u_in, south, u_out, north] } else { [u_in, north, u_out, south] };
            pd.push([row[0] as i64, row[1] as i64, row[2] as i64, row[3] as i64]);
        }
        Diagram::from_pd(&pd)
    }

    pub fn from_json(value: &Json) -> Result<Diagram, String> {
        fn ints(v: &Json) -> Result<Vec<i64>, String> {
            v.as_array().ok_or("expected an array")?.iter().map(|x| x.as_i64().ok_or_else(|| "expected an integer".to_string())).collect()
        }
        fn rows4(v: &Json) -> Result<Vec<[i64; 4]>, String> {
            let mut out = Vec::new();
            for row in v.as_array().ok_or("PD must be an array")? {
                let r = ints(row)?;
                if r.len() != 4 {
                    return Err("each crossing must have four labels".into());
                }
                out.push([r[0], r[1], r[2], r[3]]);
            }
            Ok(out)
        }
        if value.as_array().is_some() {
            return Diagram::from_pd(&rows4(value)?);
        }
        if let Some(pd) = value.get("pd") {
            return Diagram::from_pd(&rows4(pd)?);
        }
        if let Some(braid) = value.get("braid") {
            let strands = braid.get("strands").and_then(|s| s.as_i64()).ok_or("braid needs strands")?;
            let word = ints(braid.get("word").ok_or("braid needs word")?)?;
            return Diagram::from_braid(strands.max(0) as usize, &word);
        }
        if let Some(rows) = value.get("rows") {
            let mut out = Vec::new();
            for row in rows.as_array().ok_or("rows must be an array")? {
                let r = ints(row)?;
                if r.len() != 2 {
                    return Err("each grid row needs two columns".into());
                }
                out.push([r[0], r[1]]);
            }
            return Diagram::from_grid(&out);
        }
        if let (Some(x), Some(o)) = (value.get("x"), value.get("o")) {
            let (x, o) = (ints(x)?, ints(o)?);
            if x.len() != o.len() {
                return Err("x and o must have equal length".into());
            }
            let rows: Vec<[i64; 2]> = x.iter().zip(o.iter()).map(|(&a, &b)| [a, b]).collect();
            return Diagram::from_grid(&rows);
        }
        Err("specify one of pd, braid, rows, or x/o".into())
    }

    pub fn alpha(&self) -> Vec<u32> {
        let n = self.pd.len();
        let mut first = vec![u32::MAX; 2 * n];
        let mut alpha = vec![0u32; 4 * n];
        for (i, row) in self.pd.iter().enumerate() {
            for (j, &e) in row.iter().enumerate() {
                let dart = (4 * i + j) as u32;
                let e = e as usize;
                if first[e] == u32::MAX {
                    first[e] = dart;
                } else {
                    alpha[dart as usize] = first[e];
                    alpha[first[e] as usize] = dart;
                }
            }
        }
        alpha
    }

    pub fn faces(&self) -> Vec<Vec<u32>> {
        let alpha = self.alpha();
        let total = alpha.len();
        let mut seen = vec![false; total];
        let mut faces = Vec::new();
        for start in 0..total {
            if seen[start] {
                continue;
            }
            let mut face = Vec::new();
            let mut d = start as u32;
            while !seen[d as usize] {
                seen[d as usize] = true;
                face.push(d);
                d = rot(alpha[d as usize]);
            }
            faces.push(face);
        }
        faces
    }

    /// Incoming darts of an oriented traversal starting at the under-port of crossing 0.
    pub fn traversal(&self) -> Vec<u32> {
        let alpha = self.alpha();
        let mut walk = Vec::with_capacity(2 * self.pd.len());
        let mut current = 0u32;
        for _ in 0..2 * self.pd.len() {
            walk.push(current);
            current = alpha[((current & !3) | ((current + 2) & 3)) as usize];
        }
        walk
    }

    /// (incoming under slot, incoming over slot) per crossing.
    pub fn incoming_slots(&self) -> Vec<(u32, u32)> {
        let mut slots = vec![(0u32, 1u32); self.pd.len()];
        for dart in self.traversal() {
            let (c, j) = ((dart / 4) as usize, dart % 4);
            if j % 2 == 1 { slots[c].1 = j } else { slots[c].0 = j }
        }
        slots
    }

    pub fn signs(&self) -> Vec<i32> {
        self.incoming_slots().iter().map(|&(u, o)| if (o + 4 - u) % 4 == 3 { 1 } else { -1 }).collect()
    }

    pub fn writhe(&self) -> i64 {
        self.signs().iter().map(|&s| s as i64).sum()
    }

    #[allow(dead_code)]
    pub fn mirror(&self) -> Diagram {
        let rows: Vec<[i64; 4]> = self.pd.iter().map(|r| [r[1] as i64, r[2] as i64, r[3] as i64, r[0] as i64]).collect();
        Diagram::from_pd(&rows).expect("the mirror of a valid diagram is valid")
    }
}
