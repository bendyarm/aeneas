// Vendored AES-128 fixslice ENCRYPT (given expanded key) from RustCrypto aes
// v0.9.1 (aes/src/soft/fixslice32.rs, MIT/Apache-2.0). Monomorphic, no_std-able,
// cipher-crate API stripped. Gate logic VERBATIM; documented de-sugarings:
//  * ops take &mut [u32] slices per upstream (sub_bytes/shift_rows/
//      inv_shift_rows/add_round_constant_bit/xor_columns/memshift32);
//      mix_columns_* keep upstream's own &mut State
//  * from_le_bytes(x[a..b].try_into().unwrap())  -> ld_le() explicit LE assembly
//  * to_le_bytes()+copy_from_slice()             -> explicit byte array of
//      upstream's own `(w>>k) as u8` truncating casts
//  * add_round_key has upstream's (state, rkey: &[u32]) signature and the
//      encrypt/decrypt call sites pass upstream's &rkeys[..] subslices;
//      the key SCHEDULE still uses (rkeys, off) + read8/write8 wrappers
//  * shift_rows_* / add_round_key iter_mut/zip -> `for i in 0..8`
//  * memshift32 body is now VERBATIM upstream (.rev() + debug_asserts
//      restored; only the &mut [u32] -> &mut [u32; 88] signature delta remains)
//  * the encrypt round `loop{...break}` is VERBATIM upstream (recursive
//      extraction); key-schedule rcon + fold loops are `for` loops (the
//      fold's (8..72).step_by(32) -> plain-range equivalent)
//  * State::default()/BatchBlocks -> explicit [u32;8] / [[u8;16];2] literals
//  * ALL upstream debug_assert!s RESTORED verbatim, except two whose bound
//      variable no longer exists under a signature delta: bitslice's
//      output.len() (ours returns State instead of taking &mut [u32]) and
//      add_round_key's rkey.len() (ours takes (rkeys,off), see roadmap #7)
//  * cfg(aes_backend_soft="compact") branches resolved
//      to the non-compact path; aes192/aes256 and the cipher-crate API omitted
// Pristine upstream reference: tests/src/reference/fixslice32-aes-v0.9.1.rs;
// per-function audit + de-vendoring roadmap: PORTING-NOTES-ACL2.md.

type State = [u32; 8];

fn ror(x: u32, y: u32) -> u32 { x.rotate_right(y) }
fn ror_distance(rows: u32, cols: u32) -> u32 { (rows << 3) + (cols << 1) }
fn rotate_rows_1(x: u32) -> u32 { ror(x, ror_distance(1, 0)) }
fn rotate_rows_2(x: u32) -> u32 { ror(x, ror_distance(2, 0)) }
fn rotate_rows_and_columns_1_1(x: u32) -> u32 {
    (ror(x, ror_distance(1, 1)) & 0x3f3f3f3f) | (ror(x, ror_distance(0, 1)) & 0xc0c0c0c0)
}
fn rotate_rows_and_columns_1_2(x: u32) -> u32 {
    (ror(x, ror_distance(1, 2)) & 0x0f0f0f0f) | (ror(x, ror_distance(0, 2)) & 0xf0f0f0f0)
}
fn rotate_rows_and_columns_1_3(x: u32) -> u32 {
    (ror(x, ror_distance(1, 3)) & 0x03030303) | (ror(x, ror_distance(0, 3)) & 0xfcfcfcfc)
}
fn rotate_rows_and_columns_2_2(x: u32) -> u32 {
    (ror(x, ror_distance(2, 2)) & 0x0f0f0f0f) | (ror(x, ror_distance(1, 2)) & 0xf0f0f0f0)
}

fn delta_swap_1(a: &mut u32, shift: u32, mask: u32) {
    let t = (*a ^ ((*a) >> shift)) & mask;
    *a ^= t ^ (t << shift);
}
fn delta_swap_2(a: &mut u32, b: &mut u32, shift: u32, mask: u32) {
    let t = (*a ^ ((*b) >> shift)) & mask;
    *a ^= t;
    *b ^= t << shift;
}

fn sub_bytes(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);

    let u7 = state[0];
    let u6 = state[1];
    let u5 = state[2];
    let u4 = state[3];
    let u3 = state[4];
    let u2 = state[5];
    let u1 = state[6];
    let u0 = state[7];

    let y14 = u3 ^ u5;
    let y13 = u0 ^ u6;
    let y12 = y13 ^ y14;
    let t1 = u4 ^ y12;
    let y15 = t1 ^ u5;
    let t2 = y12 & y15;
    let y6 = y15 ^ u7;
    let y20 = t1 ^ u1;
    // y12 -> stack
    let y9 = u0 ^ u3;
    // y20 -> stack
    let y11 = y20 ^ y9;
    // y9 -> stack
    let t12 = y9 & y11;
    // y6 -> stack
    let y7 = u7 ^ y11;
    let y8 = u0 ^ u5;
    let t0 = u1 ^ u2;
    let y10 = y15 ^ t0;
    // y15 -> stack
    let y17 = y10 ^ y11;
    // y14 -> stack
    let t13 = y14 & y17;
    let t14 = t13 ^ t12;
    // y17 -> stack
    let y19 = y10 ^ y8;
    // y10 -> stack
    let t15 = y8 & y10;
    let t16 = t15 ^ t12;
    let y16 = t0 ^ y11;
    // y11 -> stack
    let y21 = y13 ^ y16;
    // y13 -> stack
    let t7 = y13 & y16;
    // y16 -> stack
    let y18 = u0 ^ y16;
    let y1 = t0 ^ u7;
    let y4 = y1 ^ u3;
    // u7 -> stack
    let t5 = y4 & u7;
    let t6 = t5 ^ t2;
    let t18 = t6 ^ t16;
    let t22 = t18 ^ y19;
    let y2 = y1 ^ u0;
    let t10 = y2 & y7;
    let t11 = t10 ^ t7;
    let t20 = t11 ^ t16;
    let t24 = t20 ^ y18;
    let y5 = y1 ^ u6;
    let t8 = y5 & y1;
    let t9 = t8 ^ t7;
    let t19 = t9 ^ t14;
    let t23 = t19 ^ y21;
    let y3 = y5 ^ y8;
    // y6 <- stack
    let t3 = y3 & y6;
    let t4 = t3 ^ t2;
    // y20 <- stack
    let t17 = t4 ^ y20;
    let t21 = t17 ^ t14;
    let t26 = t21 & t23;
    let t27 = t24 ^ t26;
    let t31 = t22 ^ t26;
    let t25 = t21 ^ t22;
    // y4 -> stack
    let t28 = t25 & t27;
    let t29 = t28 ^ t22;
    let z14 = t29 & y2;
    let z5 = t29 & y7;
    let t30 = t23 ^ t24;
    let t32 = t31 & t30;
    let t33 = t32 ^ t24;
    let t35 = t27 ^ t33;
    let t36 = t24 & t35;
    let t38 = t27 ^ t36;
    let t39 = t29 & t38;
    let t40 = t25 ^ t39;
    let t43 = t29 ^ t40;
    // y16 <- stack
    let z3 = t43 & y16;
    let tc12 = z3 ^ z5;
    // tc12 -> stack
    // y13 <- stack
    let z12 = t43 & y13;
    let z13 = t40 & y5;
    let z4 = t40 & y1;
    let tc6 = z3 ^ z4;
    let t34 = t23 ^ t33;
    let t37 = t36 ^ t34;
    let t41 = t40 ^ t37;
    // y10 <- stack
    let z8 = t41 & y10;
    let z17 = t41 & y8;
    let t44 = t33 ^ t37;
    // y15 <- stack
    let z0 = t44 & y15;
    // z17 -> stack
    // y12 <- stack
    let z9 = t44 & y12;
    let z10 = t37 & y3;
    let z1 = t37 & y6;
    let tc5 = z1 ^ z0;
    let tc11 = tc6 ^ tc5;
    // y4 <- stack
    let z11 = t33 & y4;
    let t42 = t29 ^ t33;
    let t45 = t42 ^ t41;
    // y17 <- stack
    let z7 = t45 & y17;
    let tc8 = z7 ^ tc6;
    // y14 <- stack
    let z16 = t45 & y14;
    // y11 <- stack
    let z6 = t42 & y11;
    let tc16 = z6 ^ tc8;
    // z14 -> stack
    // y9 <- stack
    let z15 = t42 & y9;
    let tc20 = z15 ^ tc16;
    let tc1 = z15 ^ z16;
    let tc2 = z10 ^ tc1;
    let tc21 = tc2 ^ z11;
    let tc3 = z9 ^ tc2;
    let s0 = tc3 ^ tc16;
    let s3 = tc3 ^ tc11;
    let s1 = s3 ^ tc16;
    let tc13 = z13 ^ tc1;
    // u7 <- stack
    let z2 = t33 & u7;
    let tc4 = z0 ^ z2;
    let tc7 = z12 ^ tc4;
    let tc9 = z8 ^ tc7;
    let tc10 = tc8 ^ tc9;
    // z14 <- stack
    let tc17 = z14 ^ tc10;
    let s5 = tc21 ^ tc17;
    let tc26 = tc17 ^ tc20;
    // z17 <- stack
    let s2 = tc26 ^ z17;
    // tc12 <- stack
    let tc14 = tc4 ^ tc12;
    let tc18 = tc13 ^ tc14;
    let s6 = tc10 ^ tc18;
    let s7 = z12 ^ tc18;
    let s4 = tc14 ^ s3;

    state[0] = s7;
    state[1] = s6;
    state[2] = s5;
    state[3] = s4;
    state[4] = s3;
    state[5] = s2;
    state[6] = s1;
    state[7] = s0;
}


fn sub_bytes_nots(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);
    state[0] ^= 0xffffffff;
    state[1] ^= 0xffffffff;
    state[5] ^= 0xffffffff;
    state[6] ^= 0xffffffff;
}

fn shift_rows_2(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);
    for i in 0..8 {
        let mut x = state[i];
        delta_swap_1(&mut x, 4, 0x0f000f00);
        state[i] = x;
    }
}

fn ld_le(x: &[u8; 16], o: usize) -> u32 {
    (x[o] as u32) | ((x[o + 1] as u32) << 8) | ((x[o + 2] as u32) << 16) | ((x[o + 3] as u32) << 24)
}

fn bitslice(input0: &[u8; 16], input1: &[u8; 16]) -> State {
    debug_assert_eq!(input0.len(), 16);
    debug_assert_eq!(input1.len(), 16);

    let mut t0 = ld_le(input0, 0x00);
    let mut t2 = ld_le(input0, 0x04);
    let mut t4 = ld_le(input0, 0x08);
    let mut t6 = ld_le(input0, 0x0c);
    let mut t1 = ld_le(input1, 0x00);
    let mut t3 = ld_le(input1, 0x04);
    let mut t5 = ld_le(input1, 0x08);
    let mut t7 = ld_le(input1, 0x0c);
    let m0 = 0x55555555;
    delta_swap_2(&mut t1, &mut t0, 1, m0);
    delta_swap_2(&mut t3, &mut t2, 1, m0);
    delta_swap_2(&mut t5, &mut t4, 1, m0);
    delta_swap_2(&mut t7, &mut t6, 1, m0);
    let m1 = 0x33333333;
    delta_swap_2(&mut t2, &mut t0, 2, m1);
    delta_swap_2(&mut t3, &mut t1, 2, m1);
    delta_swap_2(&mut t6, &mut t4, 2, m1);
    delta_swap_2(&mut t7, &mut t5, 2, m1);
    let m2 = 0x0f0f0f0f;
    delta_swap_2(&mut t4, &mut t0, 4, m2);
    delta_swap_2(&mut t5, &mut t1, 4, m2);
    delta_swap_2(&mut t6, &mut t2, 4, m2);
    delta_swap_2(&mut t7, &mut t3, 4, m2);
    [t0, t1, t2, t3, t4, t5, t6, t7]
}

fn inv_bitslice(input: &State) -> [[u8; 16]; 2] {
    debug_assert_eq!(input.len(), 8);

    let mut t0 = input[0];
    let mut t1 = input[1];
    let mut t2 = input[2];
    let mut t3 = input[3];
    let mut t4 = input[4];
    let mut t5 = input[5];
    let mut t6 = input[6];
    let mut t7 = input[7];
    let m0 = 0x55555555;
    delta_swap_2(&mut t1, &mut t0, 1, m0);
    delta_swap_2(&mut t3, &mut t2, 1, m0);
    delta_swap_2(&mut t5, &mut t4, 1, m0);
    delta_swap_2(&mut t7, &mut t6, 1, m0);
    let m1 = 0x33333333;
    delta_swap_2(&mut t2, &mut t0, 2, m1);
    delta_swap_2(&mut t3, &mut t1, 2, m1);
    delta_swap_2(&mut t6, &mut t4, 2, m1);
    delta_swap_2(&mut t7, &mut t5, 2, m1);
    let m2 = 0x0f0f0f0f;
    delta_swap_2(&mut t4, &mut t0, 4, m2);
    delta_swap_2(&mut t5, &mut t1, 4, m2);
    delta_swap_2(&mut t6, &mut t2, 4, m2);
    delta_swap_2(&mut t7, &mut t3, 4, m2);
    let o0 = [
        t0 as u8, (t0 >> 8) as u8, (t0 >> 16) as u8, (t0 >> 24) as u8,
        t2 as u8, (t2 >> 8) as u8, (t2 >> 16) as u8, (t2 >> 24) as u8,
        t4 as u8, (t4 >> 8) as u8, (t4 >> 16) as u8, (t4 >> 24) as u8,
        t6 as u8, (t6 >> 8) as u8, (t6 >> 16) as u8, (t6 >> 24) as u8,
    ];
    let o1 = [
        t1 as u8, (t1 >> 8) as u8, (t1 >> 16) as u8, (t1 >> 24) as u8,
        t3 as u8, (t3 >> 8) as u8, (t3 >> 16) as u8, (t3 >> 24) as u8,
        t5 as u8, (t5 >> 8) as u8, (t5 >> 16) as u8, (t5 >> 24) as u8,
        t7 as u8, (t7 >> 8) as u8, (t7 >> 16) as u8, (t7 >> 24) as u8,
    ];
    [o0, o1]
}

macro_rules! define_mix_columns {
    (
        $name:ident,
        $name_inv:ident,
        $first_rotate:path,
        $second_rotate:path
    ) => {
        #[rustfmt::skip]
        fn $name(state: &mut State) {
            let (a0, a1, a2, a3, a4, a5, a6, a7) = (
                state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]
            );
            let (b0, b1, b2, b3, b4, b5, b6, b7) = (
                $first_rotate(a0),
                $first_rotate(a1),
                $first_rotate(a2),
                $first_rotate(a3),
                $first_rotate(a4),
                $first_rotate(a5),
                $first_rotate(a6),
                $first_rotate(a7),
            );
            let (c0, c1, c2, c3, c4, c5, c6, c7) = (
                a0 ^ b0,
                a1 ^ b1,
                a2 ^ b2,
                a3 ^ b3,
                a4 ^ b4,
                a5 ^ b5,
                a6 ^ b6,
                a7 ^ b7,
            );
            state[0] = b0      ^ c7 ^ $second_rotate(c0);
            state[1] = b1 ^ c0 ^ c7 ^ $second_rotate(c1);
            state[2] = b2 ^ c1      ^ $second_rotate(c2);
            state[3] = b3 ^ c2 ^ c7 ^ $second_rotate(c3);
            state[4] = b4 ^ c3 ^ c7 ^ $second_rotate(c4);
            state[5] = b5 ^ c4      ^ $second_rotate(c5);
            state[6] = b6 ^ c5      ^ $second_rotate(c6);
            state[7] = b7 ^ c6      ^ $second_rotate(c7);
        }

        #[rustfmt::skip]
        fn $name_inv(state: &mut State) {
            let (a0, a1, a2, a3, a4, a5, a6, a7) = (
                state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]
            );
            let (b0, b1, b2, b3, b4, b5, b6, b7) = (
                $first_rotate(a0),
                $first_rotate(a1),
                $first_rotate(a2),
                $first_rotate(a3),
                $first_rotate(a4),
                $first_rotate(a5),
                $first_rotate(a6),
                $first_rotate(a7),
            );
            let (c0, c1, c2, c3, c4, c5, c6, c7) = (
                a0 ^ b0,
                a1 ^ b1,
                a2 ^ b2,
                a3 ^ b3,
                a4 ^ b4,
                a5 ^ b5,
                a6 ^ b6,
                a7 ^ b7,
            );
            let (d0, d1, d2, d3, d4, d5, d6, d7) = (
                a0      ^ c7,
                a1 ^ c0 ^ c7,
                a2 ^ c1,
                a3 ^ c2 ^ c7,
                a4 ^ c3 ^ c7,
                a5 ^ c4,
                a6 ^ c5,
                a7 ^ c6,
            );
            let (e0, e1, e2, e3, e4, e5, e6, e7) = (
                c0      ^ d6,
                c1      ^ d6 ^ d7,
                c2 ^ d0      ^ d7,
                c3 ^ d1 ^ d6,
                c4 ^ d2 ^ d6 ^ d7,
                c5 ^ d3      ^ d7,
                c6 ^ d4,
                c7 ^ d5,
            );
            state[0] = d0 ^ e0 ^ $second_rotate(e0);
            state[1] = d1 ^ e1 ^ $second_rotate(e1);
            state[2] = d2 ^ e2 ^ $second_rotate(e2);
            state[3] = d3 ^ e3 ^ $second_rotate(e3);
            state[4] = d4 ^ e4 ^ $second_rotate(e4);
            state[5] = d5 ^ e5 ^ $second_rotate(e5);
            state[6] = d6 ^ e6 ^ $second_rotate(e6);
            state[7] = d7 ^ e7 ^ $second_rotate(e7);
        }
    }
}

define_mix_columns!(
    mix_columns_0,
    inv_mix_columns_0,
    rotate_rows_1,
    rotate_rows_2
);

define_mix_columns!(
    mix_columns_1,
    inv_mix_columns_1,
    rotate_rows_and_columns_1_1,
    rotate_rows_and_columns_2_2
);


define_mix_columns!(
    mix_columns_2,
    inv_mix_columns_2,
    rotate_rows_and_columns_1_2,
    rotate_rows_2
);


define_mix_columns!(
    mix_columns_3,
    inv_mix_columns_3,
    rotate_rows_and_columns_1_3,
    rotate_rows_and_columns_2_2
);


fn add_round_key(state: &mut State, rkey: &[u32]) {
    debug_assert_eq!(rkey.len(), 8);
    // de-sugared: for (a, b) in state.iter_mut().zip(rkey) { *a ^= b; }
    for i in 0..8 {
        state[i] ^= rkey[i];
    }
}

// The 10-round `loop { ... if rk_off == 80 { break } ... }` unrolled: AES-128 has
// a statically fixed number of rounds, so this is a faithful transformation.
fn aes128_encrypt(rkeys: &[u32; 88], block0: &[u8; 16], block1: &[u8; 16]) -> [[u8; 16]; 2] {
    let mut state: State = bitslice(block0, block1);

    add_round_key(&mut state, &rkeys[..8]);

    let mut rk_off = 8;
    loop {
        sub_bytes(&mut state);
        mix_columns_1(&mut state);
        add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
        rk_off += 8;

        if rk_off == 80 {
            break;
        }

        sub_bytes(&mut state);
        mix_columns_2(&mut state);
        add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
        rk_off += 8;

        sub_bytes(&mut state);
        mix_columns_3(&mut state);
        add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
        rk_off += 8;

        sub_bytes(&mut state);
        mix_columns_0(&mut state);
        add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
        rk_off += 8;
    }

    shift_rows_2(&mut state);

    sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[80..]);

    inv_bitslice(&state)
}

/// Encrypt a single 16-byte block given the fixsliced expanded key.
pub fn encrypt_block(rkeys: [u32; 88], block: [u8; 16]) -> [u8; 16] {
    let out = aes128_encrypt(&rkeys, &block, &block);
    out[0]
}

// ----------------------------------------------------------------------------
// KEY SCHEDULE (vendored from aes128_key_schedule). The reference passes
// &mut rkeys[a..b] mutable subslices into sub_bytes / inv_shift_rows / etc.;
// we de-sugar those to read8 / process-on-State / write8 at an offset, so the
// whole [u32;88] is mutated by index (no mutable-subslice write-back). Also:
// the (8..72).step_by(32) adjustment loop -> `while`. Gate logic verbatim.

fn shift_rows_1(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);
    for i in 0..8 {
        let mut x = state[i];
        delta_swap_1(&mut x, 4, 0x0c0f0300);
        delta_swap_1(&mut x, 2, 0x33003300);
        state[i] = x;
    }
}
fn shift_rows_3(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);
    for i in 0..8 {
        let mut x = state[i];
        delta_swap_1(&mut x, 4, 0x030f0c00);
        delta_swap_1(&mut x, 2, 0x33003300);
        state[i] = x;
    }
}
fn inv_shift_rows_1(state: &mut [u32]) {
    shift_rows_3(state);
}
fn inv_shift_rows_2(state: &mut [u32]) {
    shift_rows_2(state);
}
fn inv_shift_rows_3(state: &mut [u32]) {
    shift_rows_1(state);
}

fn add_round_constant_bit(state: &mut [u32], bit: usize) {
    state[bit] ^= 0x0000c000;
}

fn read8(rkeys: &[u32; 88], off: usize) -> State {
    [
        rkeys[off], rkeys[off + 1], rkeys[off + 2], rkeys[off + 3],
        rkeys[off + 4], rkeys[off + 5], rkeys[off + 6], rkeys[off + 7],
    ]
}
fn write8(rkeys: &mut [u32; 88], off: usize, s: State) {
    for i in 0..8 {
        rkeys[off + i] = s[i];
    }
}

fn sub_bytes_at(rkeys: &mut [u32; 88], off: usize) {
    let mut s = read8(rkeys, off);
    sub_bytes(&mut s);
    write8(rkeys, off, s);
}
fn sub_bytes_nots_at(rkeys: &mut [u32; 88], off: usize) {
    let mut s = read8(rkeys, off);
    sub_bytes_nots(&mut s);
    write8(rkeys, off, s);
}
fn add_rc_bit_at(rkeys: &mut [u32; 88], off: usize, bit: usize) {
    let mut s = read8(rkeys, off);
    add_round_constant_bit(&mut s, bit);
    write8(rkeys, off, s);
}
fn inv_shift_rows_1_at(rkeys: &mut [u32; 88], off: usize) {
    let mut s = read8(rkeys, off);
    inv_shift_rows_1(&mut s);
    write8(rkeys, off, s);
}
fn inv_shift_rows_2_at(rkeys: &mut [u32; 88], off: usize) {
    let mut s = read8(rkeys, off);
    inv_shift_rows_2(&mut s);
    write8(rkeys, off, s);
}
fn inv_shift_rows_3_at(rkeys: &mut [u32; 88], off: usize) {
    let mut s = read8(rkeys, off);
    inv_shift_rows_3(&mut s);
    write8(rkeys, off, s);
}

fn memshift32(buffer: &mut [u32], src_offset: usize) {
    debug_assert_eq!(src_offset % 8, 0);

    let dst_offset = src_offset + 8;
    debug_assert!(dst_offset + 8 <= buffer.len());

    for i in (0..8).rev() {
        buffer[dst_offset + i] = buffer[src_offset + i];
    }
}

fn xor_columns(rkeys: &mut [u32], offset: usize, idx_xor: usize, idx_ror: u32) {
    for i in 0..8 {
        let off_i = offset + i;
        let rk = rkeys[off_i - idx_xor] ^ (0x03030303 & ror(rkeys[off_i], idx_ror));
        rkeys[off_i] =
            rk ^ (0xfcfcfcfc & (rk << 2)) ^ (0xf0f0f0f0 & (rk << 4)) ^ (0xc0c0c0c0 & (rk << 6));
    }
}

fn bitslice_into(rkeys: &mut [u32; 88], off: usize, in0: &[u8; 16], in1: &[u8; 16]) {
    let s = bitslice(in0, in1);
    write8(rkeys, off, s);
}

fn add_rcon(rkeys: &mut [u32; 88], rk_off: usize, rcon: usize) {
    if rcon < 8 {
        add_rc_bit_at(rkeys, rk_off, rcon);
    } else {
        add_rc_bit_at(rkeys, rk_off, rcon - 8);
        add_rc_bit_at(rkeys, rk_off, rcon - 7);
        add_rc_bit_at(rkeys, rk_off, rcon - 5);
        add_rc_bit_at(rkeys, rk_off, rcon - 4);
    }
}

// One key-expansion round, factored OUT of the rcon loop: keeping the loop
// body a single (non-recursive) call keeps the recursive loop shallow, which
// ACL2 admits quickly (a deeply-nested body in the recursive fn itself blows
// up the admission).
fn key_round(rkeys: &mut [u32; 88], rk_off_in: usize, rcon: usize) -> usize {
    memshift32(rkeys, rk_off_in);
    let rk_off = rk_off_in + 8;
    sub_bytes_at(rkeys, rk_off);
    sub_bytes_nots_at(rkeys, rk_off);
    add_rcon(rkeys, rk_off, rcon);
    xor_columns(rkeys, rk_off, 8, ror_distance(1, 3));
    rk_off
}

fn aes128_key_schedule(key: &[u8; 16]) -> [u32; 88] {
    let mut rkeys: [u32; 88] = [0u32; 88];
    bitslice_into(&mut rkeys, 0, key, key);
    // The rcon loop (10 rounds, fixed), as in RustCrypto. `-loops-to-rec` emits
    // a recursive `..._loop0` that calls key_round OPAQUELY (key_round is a
    // separate fn, not inlined), so admission stays cheap -- like the write8 /
    // memshift32 loops -- and the recursive form is what the schedule proof
    // inducts over (the earlier unroll was a workaround that is no longer needed).
    let mut rk_off = 0;
    for rcon in 0..10 {
        rk_off = key_round(&mut rkeys, rk_off, rcon);
    }
    let _ = rk_off;
    // Adjust to fixslicing format (non-compact). Upstream iterates
    // (8..72).step_by(32) = {8, 40}; step_by isn't extractable yet (roadmap),
    // so the equivalent plain-range form base = 8 + 32*k, k in 0..2 is used.
    for k in 0..2usize {
        // base = 8 + 32*k, written branch-free of loop-var multiplication
        // (k*32 sends ACL2's termination arithmetic nonlinear).
        let base = if k == 0 { 8 } else { 40 };
        inv_shift_rows_1_at(&mut rkeys, base);
        inv_shift_rows_2_at(&mut rkeys, base + 8);
        inv_shift_rows_3_at(&mut rkeys, base + 16);
    }
    inv_shift_rows_1_at(&mut rkeys, 72);
    // Account for NOTs removed from sub_bytes (i = 1..=10), as upstream;
    // the byte offset 8*i is carried additively for the same reason.
    let mut off = 8;
    for _i in 1usize..11 {
        sub_bytes_nots_at(&mut rkeys, off);
        off += 8;
    }
    let _ = off;
    rkeys
}

/// Full AES-128: expand the key and encrypt one block.
pub fn encrypt(key: [u8; 16], block: [u8; 16]) -> [u8; 16] {
    let rkeys = aes128_key_schedule(&key);
    encrypt_block(rkeys, block)
}

// ----------------------------------------------------------------------------
// DECRYPT (vendored from aes128_decrypt). inv_sub_bytes is the inverse S-box
// (verbatim). The inverse round ops (inv_mix_columns_*, inv_shift_rows_*,
// inv_bitslice) and the shared key schedule are already defined above. The
// 10-round `loop{...break}` is unrolled (fixed count), like encrypt.

fn inv_sub_bytes(state: &mut [u32]) {
    debug_assert_eq!(state.len(), 8);

    let u7 = state[0];
    let u6 = state[1];
    let u5 = state[2];
    let u4 = state[3];
    let u3 = state[4];
    let u2 = state[5];
    let u1 = state[6];
    let u0 = state[7];

    let t23 = u0 ^ u3;
    let t8 = u1 ^ t23;
    let m2 = t23 & t8;
    let t4 = u4 ^ t8;
    let t22 = u1 ^ u3;
    let t2 = u0 ^ u1;
    let t1 = u3 ^ u4;
    // t23 -> stack
    let t9 = u7 ^ t1;
    // t8 -> stack
    let m7 = t22 & t9;
    // t9 -> stack
    let t24 = u4 ^ u7;
    // m7 -> stack
    let t10 = t2 ^ t24;
    // u4 -> stack
    let m14 = t2 & t10;
    let r5 = u6 ^ u7;
    // m2 -> stack
    let t3 = t1 ^ r5;
    // t2 -> stack
    let t13 = t2 ^ r5;
    let t19 = t22 ^ r5;
    // t3 -> stack
    let t17 = u2 ^ t19;
    // t4 -> stack
    let t25 = u2 ^ t1;
    let r13 = u1 ^ u6;
    // t25 -> stack
    let t20 = t24 ^ r13;
    // t17 -> stack
    let m9 = t20 & t17;
    // t20 -> stack
    let r17 = u2 ^ u5;
    // t22 -> stack
    let t6 = t22 ^ r17;
    // t13 -> stack
    let m1 = t13 & t6;
    let y5 = u0 ^ r17;
    let m4 = t19 & y5;
    let m5 = m4 ^ m1;
    let m17 = m5 ^ t24;
    let r18 = u5 ^ u6;
    let t27 = t1 ^ r18;
    let t15 = t10 ^ t27;
    // t6 -> stack
    let m11 = t1 & t15;
    let m15 = m14 ^ m11;
    let m21 = m17 ^ m15;
    // t1 -> stack
    // t4 <- stack
    let m12 = t4 & t27;
    let m13 = m12 ^ m11;
    let t14 = t10 ^ r18;
    let m3 = t14 ^ m1;
    // m2 <- stack
    let m16 = m3 ^ m2;
    let m20 = m16 ^ m13;
    // u4 <- stack
    let r19 = u2 ^ u4;
    let t16 = r13 ^ r19;
    // t3 <- stack
    let t26 = t3 ^ t16;
    let m6 = t3 & t16;
    let m8 = t26 ^ m6;
    // t10 -> stack
    // m7 <- stack
    let m18 = m8 ^ m7;
    let m22 = m18 ^ m13;
    let m25 = m22 & m20;
    let m26 = m21 ^ m25;
    let m10 = m9 ^ m6;
    let m19 = m10 ^ m15;
    // t25 <- stack
    let m23 = m19 ^ t25;
    let m28 = m23 ^ m25;
    let m24 = m22 ^ m23;
    let m30 = m26 & m24;
    let m39 = m23 ^ m30;
    let m48 = m39 & y5;
    let m57 = m39 & t19;
    // m48 -> stack
    let m36 = m24 ^ m25;
    let m31 = m20 & m23;
    let m27 = m20 ^ m21;
    let m32 = m27 & m31;
    let m29 = m28 & m27;
    let m37 = m21 ^ m29;
    // m39 -> stack
    let m42 = m37 ^ m39;
    let m52 = m42 & t15;
    // t27 -> stack
    // t1 <- stack
    let m61 = m42 & t1;
    let p0 = m52 ^ m61;
    let p16 = m57 ^ m61;
    // m57 -> stack
    // t20 <- stack
    let m60 = m37 & t20;
    // p16 -> stack
    // t17 <- stack
    let m51 = m37 & t17;
    let m33 = m27 ^ m25;
    let m38 = m32 ^ m33;
    let m43 = m37 ^ m38;
    let m49 = m43 & t16;
    let p6 = m49 ^ m60;
    let p13 = m49 ^ m51;
    let m58 = m43 & t3;
    // t9 <- stack
    let m50 = m38 & t9;
    // t22 <- stack
    let m59 = m38 & t22;
    // p6 -> stack
    let p1 = m58 ^ m59;
    let p7 = p0 ^ p1;
    let m34 = m21 & m22;
    let m35 = m24 & m34;
    let m40 = m35 ^ m36;
    let m41 = m38 ^ m40;
    let m45 = m42 ^ m41;
    // t27 <- stack
    let m53 = m45 & t27;
    let p8 = m50 ^ m53;
    let p23 = p7 ^ p8;
    // t4 <- stack
    let m62 = m45 & t4;
    let p14 = m49 ^ m62;
    let s6 = p14 ^ p23;
    // t10 <- stack
    let m54 = m41 & t10;
    let p2 = m54 ^ m62;
    let p22 = p2 ^ p7;
    let s0 = p13 ^ p22;
    let p17 = m58 ^ p2;
    let p15 = m54 ^ m59;
    // t2 <- stack
    let m63 = m41 & t2;
    // m39 <- stack
    let m44 = m39 ^ m40;
    // p17 -> stack
    // t6 <- stack
    let m46 = m44 & t6;
    let p5 = m46 ^ m51;
    // p23 -> stack
    let p18 = m63 ^ p5;
    let p24 = p5 ^ p7;
    // m48 <- stack
    let p12 = m46 ^ m48;
    let s3 = p12 ^ p22;
    // t13 <- stack
    let m55 = m44 & t13;
    let p9 = m55 ^ m63;
    // p16 <- stack
    let s7 = p9 ^ p16;
    // t8 <- stack
    let m47 = m40 & t8;
    let p3 = m47 ^ m50;
    let p19 = p2 ^ p3;
    let s5 = p19 ^ p24;
    let p11 = p0 ^ p3;
    let p26 = p9 ^ p11;
    // t23 <- stack
    let m56 = m40 & t23;
    let p4 = m48 ^ m56;
    // p6 <- stack
    let p20 = p4 ^ p6;
    let p29 = p15 ^ p20;
    let s1 = p26 ^ p29;
    // m57 <- stack
    let p10 = m57 ^ p4;
    let p27 = p10 ^ p18;
    // p23 <- stack
    let s4 = p23 ^ p27;
    let p25 = p6 ^ p10;
    let p28 = p11 ^ p25;
    // p17 <- stack
    let s2 = p17 ^ p28;

    state[0] = s7;
    state[1] = s6;
    state[2] = s5;
    state[3] = s4;
    state[4] = s3;
    state[5] = s2;
    state[6] = s1;
    state[7] = s0;
}

fn aes128_decrypt(rkeys: &[u32; 88], block0: &[u8; 16], block1: &[u8; 16]) -> [[u8; 16]; 2] {
    let mut state: State = bitslice(block0, block1);
    add_round_key(&mut state, &rkeys[80..]);
    inv_sub_bytes(&mut state);
    inv_shift_rows_2(&mut state);
    add_round_key(&mut state, &rkeys[72..(72 + 8)]); inv_mix_columns_1(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[64..(64 + 8)]); inv_mix_columns_0(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[56..(56 + 8)]); inv_mix_columns_3(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[48..(48 + 8)]); inv_mix_columns_2(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[40..(40 + 8)]); inv_mix_columns_1(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[32..(32 + 8)]); inv_mix_columns_0(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[24..(24 + 8)]); inv_mix_columns_3(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[16..(16 + 8)]); inv_mix_columns_2(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[8..(8 + 8)]);  inv_mix_columns_1(&mut state); inv_sub_bytes(&mut state);
    add_round_key(&mut state, &rkeys[..8]);
    inv_bitslice(&state)
}

/// Decrypt one 16-byte block given the fixsliced expanded key.
pub fn decrypt_block(rkeys: [u32; 88], block: [u8; 16]) -> [u8; 16] {
    let out = aes128_decrypt(&rkeys, &block, &block);
    out[0]
}

/// Full AES-128 decryption: expand the key and decrypt one block.
pub fn decrypt(key: [u8; 16], block: [u8; 16]) -> [u8; 16] {
    let rkeys = aes128_key_schedule(&key);
    decrypt_block(rkeys, block)
}
