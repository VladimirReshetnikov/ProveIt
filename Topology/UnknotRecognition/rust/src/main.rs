//! fastunknot (Rust): exact unknot recognition.
//!
//! Pipeline: validation, Reidemeister I/II reduction, descending test, visible
//! connected-sum factorization, modular Alexander minor, width-bounded modular
//! Kauffman bracket, and the exact F2 Khovanov scan.  Every verdict is exact;
//! resource ceilings give UNKNOWN.  The worst case is exponential: this is not
//! a quasi-polynomial algorithm.
//!
//! Usage:
//!   fastunknot recognize FILE [--no-reduction] [--no-descending] [--no-factor]
//!                             [--no-modular] [--no-jones] [--jones-max-states N]
//!                             [--lifo] [--tail N] [--max-objects N] [--seconds S]
//!   fastunknot khovanov  FILE [--factor] [--lifo] [--tail N] [--max-objects N] [--seconds S]
//!   fastunknot jones     FILE
//! Add `--repeat K` to time K runs inside one process (the minimum and median are reported).

mod diagram;
mod filters;
mod json;
mod prep;
mod scan;
mod util;

use diagram::Diagram;
use filters::Jones;
use scan::{khovanov_rank, ScanError, ScanOptions, Stats};
use std::collections::BTreeMap;
use std::time::{Duration, Instant};
use util::BigUint;

struct Options {
    reduction: bool,
    descending: bool,
    factor: bool,
    modular: bool,
    jones: bool,
    jones_max_states: usize,
    minfill: bool,
    tail: usize,
    max_objects: Option<usize>,
    seconds: Option<f64>,
    repeat: usize,
    factor_rank: bool,
}

struct Verdict {
    status: &'static str,
    method: String,
    input_crossings: usize,
    reduced_crossings: usize,
    details: Vec<(String, String)>,
}

fn scan_options(o: &Options, deadline: Option<Instant>) -> ScanOptions {
    ScanOptions { minfill: o.minfill, tail: o.tail, max_objects: o.max_objects, deadline }
}

fn stats_json(s: &Stats) -> String {
    format!(
        "{{\"max_boundary\": {}, \"max_objects_before_elimination\": {}, \"max_objects_after_elimination\": {}, \"eliminations\": {}, \"compose_calls\": {}, \"compose_cache_hits\": {}, \"compose_shortcuts\": {}, \"composition_plans\": {}, \"transfer_plans\": {}, \"matchings\": {}, \"seconds_transfer\": {:.6}, \"seconds_eliminate\": {:.6}, \"seconds_linear\": {:.6}}}",
        s.max_boundary, s.max_objects_before, s.max_objects_after, s.eliminations, s.compose_calls, s.compose_cache_hits,
        s.compose_shortcuts, s.plans, s.transfer_plans, s.matchings, s.time_transfer.as_secs_f64(), s.time_eliminate.as_secs_f64(),
        s.time_linear.as_secs_f64()
    )
}

/// Verdict for one summand: Ok(Some(method)) = knotted, Ok(None) = unknot.
fn decide_factor(d: &Diagram, o: &Options, deadline: Option<Instant>, details: &mut Vec<(String, String)>) -> Result<Option<String>, String> {
    if o.modular && filters::alexander_obstruction(d) {
        return Ok(Some("alexander-modular".into()));
    }
    if o.jones {
        match filters::jones_obstruction(d, o.jones_max_states) {
            Jones::Knotted { peak_states } => {
                details.push(("jones_peak_states".into(), peak_states.to_string()));
                return Ok(Some("jones-modular".into()));
            }
            Jones::Inconclusive { .. } => details.push(("jones".into(), "\"inconclusive\"".into())),
            Jones::Skipped => details.push(("jones".into(), "\"skipped: frontier budget exhausted\"".into())),
        }
    }
    let order = prep::best_scan_order(&d.pd, 12.min(d.crossings()));
    match khovanov_rank(&d.pd, order, scan_options(o, deadline)) {
        Ok(r) => {
            details.push(("khovanov_reduced_rank".into(), (r.rank / 2).to_string()));
            details.push(("scan_stats".into(), stats_json(&r.stats)));
            Ok(if r.rank == 2 { None } else { Some("reduced-khovanov-F2-scan".into()) })
        }
        Err(ScanError::Limit(reason)) => Err(reason),
    }
}

fn recognize(input: &Diagram, o: &Options) -> Verdict {
    let deadline = o.seconds.map(|s| Instant::now() + Duration::from_secs_f64(s));
    let mut details = Vec::new();
    let n0 = input.crossings();
    let mut d = input.clone();
    if o.reduction {
        let (reduced, moves) = prep::simplify(&d);
        details.push(("reidemeister_moves".into(), moves.to_string()));
        d = reduced;
    }
    let done = |status: &'static str, method: &str, d: &Diagram, details: Vec<(String, String)>| Verdict {
        status,
        method: method.to_string(),
        input_crossings: n0,
        reduced_crossings: d.crossings(),
        details,
    };
    if d.crossings() == 0 {
        return done("UNKNOT", "reidemeister-reduction", &d, details);
    }
    if o.descending && prep::is_descending(&d) {
        return done("UNKNOT", "descending-diagram", &d, details);
    }
    let mut factors = if o.factor { prep::visible_factors(&d) } else { vec![d.clone()] };
    factors.sort_by_key(|f| f.crossings());
    details.push(("visible_factors".into(), factors.len().to_string()));
    let many = factors.len() > 1;
    for factor in &factors {
        let mut f = factor.clone();
        if many && o.reduction {
            f = prep::simplify(&f).0;
        }
        if f.crossings() == 0 || (many && o.descending && prep::is_descending(&f)) {
            continue;
        }
        match decide_factor(&f, o, deadline, &mut details) {
            Ok(Some(method)) => {
                let method = if many { format!("connected-sum-factor:{}", method) } else { method };
                return done("KNOTTED", &method, &d, details);
            }
            Ok(None) => {}
            Err(reason) => {
                details.push(("reason".into(), format!("\"{}\"", reason)));
                return done("UNKNOWN", "resource-limit", &d, details);
            }
        }
    }
    let method = if many { "connected-sum-all-factors-trivial" } else { "reduced-khovanov-F2-scan" };
    done("UNKNOT", method, &d, details)
}

fn timed<T>(repeat: usize, mut f: impl FnMut() -> T) -> (T, f64, f64) {
    let mut samples = Vec::with_capacity(repeat);
    let mut last = None;
    for _ in 0..repeat.max(1) {
        let t = Instant::now();
        last = Some(f());
        samples.push(t.elapsed().as_secs_f64());
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (last.unwrap(), samples[0], samples[samples.len() / 2])
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: fastunknot (recognize|khovanov|jones) FILE [options]");
        std::process::exit(2);
    }
    let mut o = Options {
        reduction: true,
        descending: true,
        factor: true,
        modular: true,
        jones: true,
        jones_max_states: 4096,
        minfill: true,
        tail: 0,
        max_objects: None,
        seconds: None,
        repeat: 1,
        factor_rank: false,
    };
    let mut i = 2;
    let number = |i: &mut usize| -> f64 {
        *i += 1;
        args.get(*i).and_then(|s| s.parse::<f64>().ok()).unwrap_or_else(|| {
            eprintln!("option {} needs a number", args[*i - 1]);
            std::process::exit(2)
        })
    };
    while i < args.len() {
        match args[i].as_str() {
            "--no-reduction" => o.reduction = false,
            "--no-descending" => o.descending = false,
            "--no-factor" => o.factor = false,
            "--no-modular" | "--no-alexander" => o.modular = false,
            "--no-jones" => o.jones = false,
            "--lifo" => o.minfill = false,
            "--factor" => o.factor_rank = true,
            "--jones-max-states" => o.jones_max_states = number(&mut i) as usize,
            "--tail" => o.tail = number(&mut i) as usize,
            "--max-objects" => o.max_objects = Some(number(&mut i) as usize),
            "--seconds" => o.seconds = Some(number(&mut i)),
            "--repeat" => o.repeat = number(&mut i) as usize,
            other => {
                eprintln!("unknown option {}", other);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let text = match std::fs::read_to_string(&args[1]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {}", args[1], e);
            std::process::exit(2);
        }
    };
    let diagram = match json::parse(&text).and_then(|v| Diagram::from_json(&v)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("invalid input: {}", e);
            std::process::exit(2);
        }
    };
    match args[0].as_str() {
        "recognize" => {
            let (v, best, median) = timed(o.repeat, || recognize(&diagram, &o));
            let details: Vec<String> = v.details.iter().map(|(k, val)| format!("\"{}\": {}", k, val)).collect();
            println!(
                "{{\"status\": \"{}\", \"method\": \"{}\", \"input_crossings\": {}, \"reduced_crossings\": {}, \"seconds\": {:.9}, \"seconds_min\": {:.9}, \"quasipolynomial_guarantee\": false, \"evidence\": {{{}}}}}",
                v.status, v.method, v.input_crossings, v.reduced_crossings, median, best, details.join(", ")
            );
            std::process::exit(if v.status == "UNKNOWN" { 3 } else { 0 });
        }
        "khovanov" => {
            let run = || -> Result<(BigUint, BTreeMap<u32, BigUint>, Stats, usize), String> {
                let deadline = o.seconds.map(|s| Instant::now() + Duration::from_secs_f64(s));
                let factors = if o.factor_rank { prep::visible_factors(&diagram) } else { vec![diagram.clone()] };
                let mut reduced: BTreeMap<u32, BigUint> = BTreeMap::new();
                reduced.insert(0, BigUint::from_u64(1));
                let mut memo: Vec<(Diagram, BTreeMap<u32, u64>)> = Vec::new();
                let mut stats = Stats::default();
                for f in &factors {
                    let by_degree = match memo.iter().find(|(d, _)| d == f) {
                        Some((_, r)) => r.clone(),
                        None => {
                            let order = prep::best_scan_order(&f.pd, 12.min(f.crossings()));
                            let r = khovanov_rank(&f.pd, order, scan_options(&o, deadline)).map_err(|ScanError::Limit(s)| s)?;
                            stats = r.stats.clone();
                            memo.push((f.clone(), r.by_degree.clone()));
                            r.by_degree
                        }
                    };
                    let mut next: BTreeMap<u32, BigUint> = BTreeMap::new();
                    for (h, v) in &reduced {
                        for (k, w) in &by_degree {
                            let term = v.mul_small(w / 2);
                            let slot = next.entry(h + k).or_insert_with(|| BigUint::from_u64(0));
                            *slot = slot.add(&term);
                        }
                    }
                    reduced = next;
                }
                let total = reduced.values().fold(BigUint::from_u64(0), |acc, v| acc.add(v));
                Ok((total, reduced, stats, factors.len()))
            };
            let (result, best, median) = timed(o.repeat, run);
            match result {
                Ok((total, reduced, stats, factors)) => {
                    let degrees: Vec<String> = reduced.iter().map(|(h, v)| format!("\"{}\": {}", h, v)).collect();
                    println!(
                        "{{\"reduced_rank\": {}, \"rank\": {}, \"reduced_by_degree\": {{{}}}, \"factors\": {}, \"seconds\": {:.9}, \"seconds_min\": {:.9}, \"stats\": {}}}",
                        total, total.mul_small(2), degrees.join(", "), factors, median, best, stats_json(&stats)
                    );
                }
                Err(reason) => {
                    println!("{{\"status\": \"UNKNOWN\", \"reason\": \"{}\", \"seconds\": {:.9}}}", reason, median);
                    std::process::exit(3);
                }
            }
        }
        "jones" => {
            let (result, best, median) = timed(o.repeat, || filters::jones_obstruction(&diagram, usize::MAX));
            let (verdict, peak) = match result {
                Jones::Knotted { peak_states } => ("KNOTTED", peak_states),
                Jones::Inconclusive { peak_states } => ("INCONCLUSIVE", peak_states),
                Jones::Skipped => ("SKIPPED", 0),
            };
            println!("{{\"verdict\": \"{}\", \"peak_states\": {}, \"seconds\": {:.9}, \"seconds_min\": {:.9}}}", verdict, peak, median, best);
        }
        other => {
            eprintln!("unknown command {}", other);
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn braid(strands: usize, word: &[i64]) -> Diagram {
        Diagram::from_braid(strands, word).unwrap()
    }

    fn reduced_rank(d: &Diagram, minfill: bool, tail: usize) -> u64 {
        let order = prep::best_scan_order(&d.pd, 12);
        let options = ScanOptions { minfill, tail, max_objects: None, deadline: None };
        match khovanov_rank(&d.pd, order, options) {
            Ok(r) => r.rank / 2,
            Err(_) => panic!("unexpected limit"),
        }
    }

    fn defaults() -> Options {
        Options { reduction: true, descending: true, factor: true, modular: true, jones: true, jones_max_states: 4096,
                  minfill: true, tail: 0, max_objects: None, seconds: None, repeat: 1, factor_rank: false }
    }

    #[test]
    fn known_ranks_in_every_configuration() {
        let t35: Vec<i64> = [1, 2].repeat(5);
        let cases: Vec<(Diagram, u64)> = vec![
            (braid(2, &[1, 1, 1]), 3),
            (braid(3, &[1, -2, 1, -2]), 5),
            (braid(3, &t35), 7),
            (braid(3, &[-2, -2, -2, 2, 1, 1, 2, 1]), 1),
            (braid(3, &[-2, -2, 1, 2, 2, 2]), 1),
            (braid(2, &[1]), 1),
            (braid(5, &[1, 2, 3, 4]), 1),
        ];
        for (d, rank) in &cases {
            for minfill in [true, false] {
                for tail in [0, 1, 2] {
                    assert_eq!(reduced_rank(d, minfill, tail), *rank);
                }
            }
            assert_eq!(reduced_rank(&d.mirror(), true, 0), *rank);
        }
    }

    #[test]
    fn invalid_inputs_are_rejected() {
        assert!(Diagram::from_braid(3, &[1]).is_err());
        assert!(Diagram::from_pd(&[[0, 1, 2, 3], [1, 0, 3, 2]]).is_err());
        assert!(Diagram::from_pd(&[[0, 1, 2, 3], [2, 1, 0, 3]]).is_err());
        assert!(Diagram::from_pd(&[[1, 2, 3, 4]]).is_err());
    }

    #[test]
    fn filters_are_one_sided() {
        let unknots = [braid(2, &[1]), braid(2, &[-1]), braid(3, &[-1, 2]), braid(3, &[-2, -2, -2, 2, 1, 1, 2, 1]),
                       braid(4, &[1, -2, 3, 2, -2, -3, 3])];
        for d in &unknots {
            for x in [d.clone(), d.mirror()] {
                assert!(!filters::alexander_obstruction(&x));
                assert!(matches!(filters::jones_obstruction(&x, usize::MAX), Jones::Inconclusive { .. }));
            }
        }
        assert!(filters::alexander_obstruction(&braid(2, &[1, 1, 1])));
        assert!(matches!(filters::jones_obstruction(&braid(2, &[1, 1, 1]), usize::MAX), Jones::Knotted { .. }));
        assert!(matches!(filters::jones_obstruction(&braid(3, &[1, -2, 1, -2]), 1), Jones::Skipped));
    }

    #[test]
    fn recognition_pipeline() {
        let o = defaults();
        assert_eq!(recognize(&braid(3, &[-2, -2, -2, 2, 1, 1, 2, 1]), &o).status, "UNKNOT");
        assert_eq!(recognize(&braid(2, &[1, 1, 1]), &o).status, "KNOTTED");
        let mut exact = defaults();
        exact.modular = false;
        exact.jones = false;
        let v = recognize(&braid(3, &[1, -2, 1, -2]), &exact);
        assert_eq!((v.status, v.method.as_str()), ("KNOTTED", "reduced-khovanov-F2-scan"));
        exact.max_objects = Some(2);
        assert_eq!(recognize(&braid(3, &[1, -2, 1, -2]), &exact).status, "UNKNOWN");
        // trefoil # trefoil splits into two visible factors
        assert_eq!(prep::visible_factors(&braid(3, &[1, 1, 1, 2, 2, 2])).len(), 2);
        // a long reducible chain disappears under R1 moves
        let chain: Vec<i64> = (1..=300).collect();
        assert_eq!(prep::simplify(&braid(301, &chain)).0.crossings(), 0);
    }
}
