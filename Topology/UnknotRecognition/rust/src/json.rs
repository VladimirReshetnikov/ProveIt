//! A minimal JSON reader, sufficient for the diagram input formats, so that the
//! crate has no dependencies.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(map) => map.get(key),
            _ => None,
        }
    }
    pub fn as_array(&self) -> Option<&Vec<Json>> {
        match self {
            Json::Arr(items) => Some(items),
            _ => None,
        }
    }
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Json::Num(x) if x.fract() == 0.0 && x.abs() < 9.0e15 => Some(*x as i64),
            _ => None,
        }
    }
}

pub fn parse(text: &str) -> Result<Json, String> {
    let bytes = text.as_bytes();
    let mut pos = 0;
    let value = value(bytes, &mut pos)?;
    skip(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(format!("trailing characters at byte {}", pos));
    }
    Ok(value)
}

fn skip(b: &[u8], pos: &mut usize) {
    while *pos < b.len() && (b[*pos] as char).is_whitespace() {
        *pos += 1;
    }
}

fn value(b: &[u8], pos: &mut usize) -> Result<Json, String> {
    skip(b, pos);
    if *pos >= b.len() {
        return Err("unexpected end of input".into());
    }
    match b[*pos] {
        b'{' => {
            *pos += 1;
            let mut map = BTreeMap::new();
            skip(b, pos);
            if *pos < b.len() && b[*pos] == b'}' {
                *pos += 1;
                return Ok(Json::Obj(map));
            }
            loop {
                skip(b, pos);
                let key = match value(b, pos)? {
                    Json::Str(s) => s,
                    _ => return Err("object keys must be strings".into()),
                };
                skip(b, pos);
                if *pos >= b.len() || b[*pos] != b':' {
                    return Err("expected ':'".into());
                }
                *pos += 1;
                let v = value(b, pos)?;
                map.insert(key, v);
                skip(b, pos);
                match b.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b'}') => {
                        *pos += 1;
                        return Ok(Json::Obj(map));
                    }
                    _ => return Err("expected ',' or '}'".into()),
                }
            }
        }
        b'[' => {
            *pos += 1;
            let mut items = Vec::new();
            skip(b, pos);
            if *pos < b.len() && b[*pos] == b']' {
                *pos += 1;
                return Ok(Json::Arr(items));
            }
            loop {
                items.push(value(b, pos)?);
                skip(b, pos);
                match b.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b']') => {
                        *pos += 1;
                        return Ok(Json::Arr(items));
                    }
                    _ => return Err("expected ',' or ']'".into()),
                }
            }
        }
        b'"' => {
            *pos += 1;
            let mut out = String::new();
            while *pos < b.len() && b[*pos] != b'"' {
                if b[*pos] == b'\\' && *pos + 1 < b.len() {
                    *pos += 1;
                    match b[*pos] {
                        b'n' => out.push('\n'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hex = std::str::from_utf8(&b[*pos + 1..(*pos + 5).min(b.len())]).unwrap_or("");
                            let code = u32::from_str_radix(hex, 16).map_err(|_| "bad \\u escape")?;
                            out.push(char::from_u32(code).unwrap_or('?'));
                            *pos += 4;
                        }
                        c => out.push(c as char),
                    }
                    *pos += 1;
                } else {
                    let start = *pos;
                    while *pos < b.len() && b[*pos] != b'"' && b[*pos] != b'\\' {
                        *pos += 1;
                    }
                    out.push_str(std::str::from_utf8(&b[start..*pos]).map_err(|_| "invalid UTF-8")?);
                }
            }
            if *pos >= b.len() {
                return Err("unterminated string".into());
            }
            *pos += 1;
            Ok(Json::Str(out))
        }
        b't' if b[*pos..].starts_with(b"true") => {
            *pos += 4;
            Ok(Json::Bool(true))
        }
        b'f' if b[*pos..].starts_with(b"false") => {
            *pos += 5;
            Ok(Json::Bool(false))
        }
        b'n' if b[*pos..].starts_with(b"null") => {
            *pos += 4;
            Ok(Json::Null)
        }
        _ => {
            let start = *pos;
            while *pos < b.len() && matches!(b[*pos], b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                *pos += 1;
            }
            let text = std::str::from_utf8(&b[start..*pos]).unwrap_or("");
            text.parse::<f64>().map(Json::Num).map_err(|_| format!("invalid number at byte {}", start))
        }
    }
}
