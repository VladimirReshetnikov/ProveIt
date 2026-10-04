//! One-sided knottedness filters in the prime field F_p, p = 2^61 - 1.
//! Either can answer KNOTTED; agreement with the unknot's value is inconclusive.

use crate::diagram::Diagram;
use crate::prep::best_scan_order;
use crate::util::{addmod, invmod, mulmod, powmod, submod, Dsu, FxMap, P61};

/// Generic evaluation points of large multiplicative order (2 has order 61 modulo
/// 2^61 - 1, which makes {+-2^k} a small structured set that torus-like invariants hit).
const ALEXANDER_T: u64 = 0x2545F4914F6CDD1D % P61;
const JONES_A: u64 = 0x9E3779B97F4A7C15 % P61;

pub const SMOOTHINGS: [[(usize, usize); 2]; 2] = [[(0, 1), (2, 3)], [(0, 3), (1, 2)]];

/// First Alexander minor evaluated at t = -1 and at a generic point.  For the unknot it is a
/// unit +-t^k (0 <= k < n), so any other value proves the knot nontrivial.
pub fn alexander_obstruction(diagram: &Diagram) -> bool {
    let n = diagram.crossings();
    if n < 2 {
        return false;
    }
    let mut arcs = Dsu::new(2 * n);
    for row in &diagram.pd {
        arcs.union(row[1] as usize, row[3] as usize);
    }
    let mut column: FxMap<usize, usize> = FxMap::default();
    for e in 0..2 * n {
        let r = arcs.find(e);
        let next = column.len();
        column.entry(r).or_insert(next);
    }
    if column.len() != n {
        return false; // not expected for a valid knot diagram; stay inconclusive
    }
    let signs = diagram.signs();
    let slots = diagram.incoming_slots();
    for t in [P61 - 1, ALEXANDER_T] {
        let one_minus_t = submod(1, t);
        let minus_one = P61 - 1;
        let m = n - 1;
        let mut a = vec![0u64; m * m];
        for i in 0..m {
            let row = &diagram.pd[i];
            let u_slot = slots[i].0 as usize;
            let o = column[&arcs.find(row[1] as usize)];
            let u = column[&arcs.find(row[u_slot] as usize)];
            let v = column[&arcs.find(row[(u_slot + 2) % 4] as usize)];
            let entries = if signs[i] > 0 { [(o, one_minus_t), (u, t), (v, minus_one)] } else { [(o, one_minus_t), (u, minus_one), (v, t)] };
            for (col, value) in entries {
                if col < m {
                    a[i * m + col] = addmod(a[i * m + col], value);
                }
            }
        }
        let det = determinant(&mut a, m);
        let mut unit = false;
        let mut term = 1u64;
        for _ in 0..n {
            if det == term || det == submod(0, term) {
                unit = true;
                break;
            }
            term = mulmod(term, t);
        }
        if !unit {
            return true;
        }
    }
    false
}

fn determinant(a: &mut [u64], n: usize) -> u64 {
    let mut det = 1u64;
    for k in 0..n {
        let pivot_row = match (k..n).find(|&i| a[i * n + k] != 0) {
            Some(r) => r,
            None => return 0,
        };
        if pivot_row != k {
            for j in 0..n {
                a.swap(k * n + j, pivot_row * n + j);
            }
            det = submod(0, det);
        }
        let pivot = a[k * n + k];
        det = mulmod(det, pivot);
        let inv = invmod(pivot);
        for i in k + 1..n {
            let f = a[i * n + k];
            if f == 0 {
                continue;
            }
            let factor = mulmod(f, inv);
            for j in k + 1..n {
                let pk = a[k * n + j];
                if pk != 0 {
                    a[i * n + j] = submod(a[i * n + j], mulmod(factor, pk));
                }
            }
            a[i * n + k] = 0;
        }
    }
    det
}

pub enum Jones {
    Knotted { peak_states: usize },
    Inconclusive { peak_states: usize },
    Skipped,
}

/// Kauffman bracket at a generic A by scanning; partial states with the same boundary
/// matching are summed at once, so the work is bounded by the number of
/// crossingless matchings of the boundary, with no multiplicity factor.
pub fn jones_obstruction(diagram: &Diagram, max_states: usize) -> Jones {
    let pd = &diagram.pd;
    let n = pd.len();
    if n == 0 {
        return Jones::Inconclusive { peak_states: 1 };
    }
    let a = JONES_A;
    let inv_a = invmod(a);
    let delta = submod(0, addmod(mulmod(a, a), mulmod(inv_a, inv_a)));
    let delta_pow = [1, delta, mulmod(delta, delta), mulmod(delta, mulmod(delta, delta)), powmod(delta, 4)];
    let order = best_scan_order(pd, 12.min(n));
    let mut states: FxMap<Vec<(u32, u32)>, u64> = FxMap::default();
    states.insert(Vec::new(), 1);
    let mut on_boundary = vec![false; 2 * n];
    let mut peak = 1usize;
    let mut labels: Vec<u32> = Vec::with_capacity(64);
    for &index in &order {
        let slots = pd[index];
        for &e in &slots {
            on_boundary[e as usize] = !on_boundary[e as usize];
        }
        let mut next: FxMap<Vec<(u32, u32)>, u64> = FxMap::default();
        for (matching, &coefficient) in &states {
            // local indices: matching points, then the four slot labels
            labels.clear();
            for &(p, q) in matching {
                labels.push(p);
                labels.push(q);
            }
            let base = labels.len();
            let mut slot_index = [0usize; 4];
            for (j, &s) in slots.iter().enumerate() {
                slot_index[j] = match labels.iter().position(|&l| l == s) {
                    Some(k) => k,
                    None => {
                        labels.push(s);
                        labels.len() - 1
                    }
                };
            }
            for (smoothing, weight) in [(0usize, a), (1usize, inv_a)] {
                let mut dsu = Dsu::new(labels.len());
                for k in (0..base).step_by(2) {
                    dsu.union(k, k + 1);
                }
                for &(x, y) in &SMOOTHINGS[smoothing] {
                    dsu.union(slot_index[x], slot_index[y]);
                }
                let mut ends: Vec<(usize, u32)> = Vec::with_capacity(labels.len());
                let mut has_end = vec![false; labels.len()];
                for k in 0..labels.len() {
                    if on_boundary[labels[k] as usize] {
                        let r = dsu.find(k);
                        has_end[r] = true;
                        ends.push((r, labels[k]));
                    }
                }
                let mut closed = 0;
                for k in 0..labels.len() {
                    if dsu.find(k) == k && !has_end[k] {
                        closed += 1;
                    }
                }
                ends.sort_unstable();
                let mut target: Vec<(u32, u32)> = ends.chunks(2).map(|c| (c[0].1.min(c[1].1), c[0].1.max(c[1].1))).collect();
                target.sort_unstable();
                let value = mulmod(mulmod(coefficient, weight), delta_pow[closed]);
                let slot = next.entry(target).or_insert(0);
                *slot = addmod(*slot, value);
            }
            if next.len() > max_states {
                return Jones::Skipped;
            }
        }
        next.retain(|_, v| *v != 0);
        states = next;
        peak = peak.max(states.len());
    }
    let bracket = *states.get(&Vec::new()).unwrap_or(&0);
    let w = diagram.writhe();
    let base = submod(0, powmod(a, 3));
    let exponent = w.rem_euclid((P61 - 1) as i64) as u64;
    let expected = mulmod(delta, powmod(base, exponent));
    if bracket == expected { Jones::Inconclusive { peak_states: peak } } else { Jones::Knotted { peak_states: peak } }
}
