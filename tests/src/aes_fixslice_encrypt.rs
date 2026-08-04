// Vendored AES-128 fixslice ENCRYPT (given expanded key) from RustCrypto aes
// v0.9.1 (aes/src/soft/fixslice32.rs, MIT/Apache-2.0). Monomorphic, no_std-able,
// cipher-crate API stripped. Gate logic VERBATIM; documented de-sugarings:
//  * &mut [u32] -> &mut State ([u32;8]) on sub_bytes/mix_columns/shift_rows
//  * from_le_bytes(x[a..b].try_into().unwrap())  -> ld_le() explicit LE assembly
//  * to_le_bytes()+copy_from_slice()             -> explicit byte array (masked
//      narrowing casts `(w>>k) as u8` -> `((w>>k)&0xff) as u8` to match the
//      checked-cast model; semantically identical truncation)
//  * add_round_key(&mut rkeys[o..o+8]) -> (rkeys:&[u32;88], off) + index
//  * shift_rows_2 iter_mut -> `for i in 0..8`
//  * the 10-round `loop{...break}` -> unrolled (statically fixed trip count)
//  * State::default()/BatchBlocks -> explicit [u32;8] / [[u8;16];2] literals

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

fn sub_bytes(state: &mut State) {
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


fn sub_bytes_nots(state: &mut State) {
    state[0] ^= 0xffffffff;
    state[1] ^= 0xffffffff;
    state[5] ^= 0xffffffff;
    state[6] ^= 0xffffffff;
}

fn shift_rows_2(state: &mut State) {
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
        (t0 & 0xff) as u8, ((t0 >> 8) & 0xff) as u8, ((t0 >> 16) & 0xff) as u8, ((t0 >> 24) & 0xff) as u8,
        (t2 & 0xff) as u8, ((t2 >> 8) & 0xff) as u8, ((t2 >> 16) & 0xff) as u8, ((t2 >> 24) & 0xff) as u8,
        (t4 & 0xff) as u8, ((t4 >> 8) & 0xff) as u8, ((t4 >> 16) & 0xff) as u8, ((t4 >> 24) & 0xff) as u8,
        (t6 & 0xff) as u8, ((t6 >> 8) & 0xff) as u8, ((t6 >> 16) & 0xff) as u8, ((t6 >> 24) & 0xff) as u8,
    ];
    let o1 = [
        (t1 & 0xff) as u8, ((t1 >> 8) & 0xff) as u8, ((t1 >> 16) & 0xff) as u8, ((t1 >> 24) & 0xff) as u8,
        (t3 & 0xff) as u8, ((t3 >> 8) & 0xff) as u8, ((t3 >> 16) & 0xff) as u8, ((t3 >> 24) & 0xff) as u8,
        (t5 & 0xff) as u8, ((t5 >> 8) & 0xff) as u8, ((t5 >> 16) & 0xff) as u8, ((t5 >> 24) & 0xff) as u8,
        (t7 & 0xff) as u8, ((t7 >> 8) & 0xff) as u8, ((t7 >> 16) & 0xff) as u8, ((t7 >> 24) & 0xff) as u8,
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


fn add_round_key(state: &mut State, rkeys: &[u32; 88], off: usize) {
    // de-sugared: for (a,b) in state.iter_mut().zip(&rkeys[off..off+8]) { *a ^= b; }
    for i in 0..8 {
        state[i] ^= rkeys[off + i];
    }
}

// The 10-round `loop { ... if rk_off == 80 { break } ... }` unrolled: AES-128 has
// a statically fixed number of rounds, so this is a faithful transformation.
fn aes128_encrypt(rkeys: &[u32; 88], block0: &[u8; 16], block1: &[u8; 16]) -> [[u8; 16]; 2] {
    let mut state: State = bitslice(block0, block1);
    add_round_key(&mut state, rkeys, 0);
    sub_bytes(&mut state); mix_columns_1(&mut state); add_round_key(&mut state, rkeys, 8);
    sub_bytes(&mut state); mix_columns_2(&mut state); add_round_key(&mut state, rkeys, 16);
    sub_bytes(&mut state); mix_columns_3(&mut state); add_round_key(&mut state, rkeys, 24);
    sub_bytes(&mut state); mix_columns_0(&mut state); add_round_key(&mut state, rkeys, 32);
    sub_bytes(&mut state); mix_columns_1(&mut state); add_round_key(&mut state, rkeys, 40);
    sub_bytes(&mut state); mix_columns_2(&mut state); add_round_key(&mut state, rkeys, 48);
    sub_bytes(&mut state); mix_columns_3(&mut state); add_round_key(&mut state, rkeys, 56);
    sub_bytes(&mut state); mix_columns_0(&mut state); add_round_key(&mut state, rkeys, 64);
    sub_bytes(&mut state); mix_columns_1(&mut state); add_round_key(&mut state, rkeys, 72);
    shift_rows_2(&mut state);
    sub_bytes(&mut state);
    add_round_key(&mut state, rkeys, 80);
    inv_bitslice(&state)
}

/// Encrypt a single 16-byte block given the fixsliced expanded key.
pub fn encrypt_block(rkeys: [u32; 88], block: [u8; 16]) -> [u8; 16] {
    let out = aes128_encrypt(&rkeys, &block, &block);
    out[0]
}
