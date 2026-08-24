/*
 * Native evaluator for the finite three-progression-free permutation count.
 *
 * This implements the same extension recurrence as `fastReflectedMLean`.
 * `used` records the entries already emitted.  `forbidden` records every z
 * for which earlier emitted values a,b satisfy a + z = 2b, so an extension x
 * is legal exactly when its bit is absent from both masks.  The recurrence is
 * memoized independently after each fixed pair of initial entries.  Value
 * complementation permits restriction to half of the possible first entries.
 *
 * The source deliberately needs no platform headers: Lake passes it directly
 * to Lean's C compiler while linking the shared certificate support library.
 */

typedef __SIZE_TYPE__ usize;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef struct lean_object lean_object;
typedef lean_object *lean_obj_arg;
typedef lean_object *lean_obj_res;

extern void *malloc(usize size);
extern void *calloc(usize count, usize size);
extern void free(void *pointer);

static usize lean_ramsey_unbox(lean_obj_arg value) {
  return ((usize)value) >> 1;
}

static lean_obj_res lean_ramsey_box(usize value) {
  return (lean_obj_res)((value << 1) | 1);
}

struct lean_ramsey_counter {
  u32 n;
  u32 full;
  usize capacity;
  usize mask;
  u16 generation;
  u16 *tags;
  u64 *keys;
  u32 *values;
  u32 *reflections;
};

static usize lean_ramsey_hash(const struct lean_ramsey_counter *counter,
    u64 key) {
  return (usize)((key * 11400714819323198485ull) >> (60 - counter->n));
}

static u32 lean_ramsey_visit(struct lean_ramsey_counter *counter,
    u32 used, u32 forbidden) {
  if (used == counter->full) {
    return 1;
  }

  const u64 key = ((u64)used << counter->n) | forbidden;
  usize slot = lean_ramsey_hash(counter, key);
  usize probes = 0;
  while (probes < counter->capacity &&
      counter->tags[slot] == counter->generation) {
    if (counter->keys[slot] == key) {
      return counter->values[slot];
    }
    slot = (slot + 1) & counter->mask;
    ++probes;
  }

  u64 total = 0;
  u32 available = counter->full & ~used & ~forbidden;
  while (available != 0) {
    const u32 bit = available & (0u - available);
    available -= bit;
    const u32 x = (u32)__builtin_ctz(bit);
    const u32 reflected =
      counter->reflections[((usize)x << counter->n) | used];
    total += lean_ramsey_visit(counter, used | bit, forbidden | reflected);
  }

  /* Descendants may have occupied the originally empty slot. */
  slot = lean_ramsey_hash(counter, key);
  probes = 0;
  while (probes < counter->capacity &&
      counter->tags[slot] == counter->generation) {
    if (counter->keys[slot] == key) {
      return counter->values[slot];
    }
    slot = (slot + 1) & counter->mask;
    ++probes;
  }
  if (probes < counter->capacity) {
    counter->tags[slot] = counter->generation;
    counter->keys[slot] = key;
    counter->values[slot] = (u32)total;
  }
  return (u32)total;
}

static int lean_ramsey_initialize(struct lean_ramsey_counter *counter, u32 n) {
  counter->n = n;
  counter->full = ((u32)1 << n) - 1;
  counter->capacity = (usize)1 << (n + 4);
  counter->mask = counter->capacity - 1;
  counter->generation = 0;
  counter->tags = (u16 *)calloc(counter->capacity, sizeof(u16));
  counter->keys = (u64 *)malloc(counter->capacity * sizeof(u64));
  counter->values = (u32 *)malloc(counter->capacity * sizeof(u32));
  counter->reflections =
    (u32 *)malloc(((usize)n << n) * sizeof(u32));
  if (counter->tags == 0 || counter->keys == 0 || counter->values == 0 ||
      counter->reflections == 0) {
    return 0;
  }

  for (u32 x = 0; x < n; ++x) {
    u32 *row = counter->reflections + ((usize)x << n);
    row[0] = 0;
    for (u32 used = 1; used <= counter->full; ++used) {
      const u32 bit = used & (0u - used);
      const u32 a = (u32)__builtin_ctz(bit);
      const int z = (int)(2 * x) - (int)a;
      row[used] = row[used - bit] |
        ((0 <= z && z < (int)n) ? (u32)1 << z : 0);
    }
  }
  return 1;
}

static void lean_ramsey_destroy(struct lean_ramsey_counter *counter) {
  free(counter->tags);
  free(counter->keys);
  free(counter->values);
  free(counter->reflections);
}

lean_obj_res lean_ramsey_fast_reflected_m(lean_obj_arg boxed_n) {
  const u32 n = (u32)lean_ramsey_unbox(boxed_n);
  if (n == 0 || n == 1) {
    return lean_ramsey_box(1);
  }

  struct lean_ramsey_counter counter;
  if (!lean_ramsey_initialize(&counter, n)) {
    lean_ramsey_destroy(&counter);
    return lean_ramsey_box(0);
  }

  u64 grand_total = 0;
  for (u32 first = 0; first < (n + 1) / 2; ++first) {
    u64 branch_total = 0;
    for (u32 second = 0; second < n; ++second) {
      if (second == first) {
        continue;
      }
      u32 forbidden = 0;
      const int reflected = (int)(2 * second) - (int)first;
      if (0 <= reflected && reflected < (int)n) {
        forbidden |= (u32)1 << reflected;
      }
      ++counter.generation;
      const u32 used = ((u32)1 << first) | ((u32)1 << second);
      branch_total += lean_ramsey_visit(&counter, used, forbidden);
    }
    grand_total += (2 * first + 1 == n) ? branch_total : 2 * branch_total;
  }

  lean_ramsey_destroy(&counter);
  return lean_ramsey_box((usize)grand_total);
}

/* The interpreter asks for the boxed symbol of the Lean external declaration.
 * Defining it here lets a tiny shim library provide the counter without
 * precompiling the large Mathlib dependency closure of ThreeFreeCounting. */
lean_obj_res
lp_ProveIt_LeanProofs_RamseyPaperCommon_fastReflectedMNative___boxed(
    lean_obj_arg boxed_n) {
  return lean_ramsey_fast_reflected_m(boxed_n);
}
