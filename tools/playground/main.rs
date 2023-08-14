//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use rand::prelude::*;
use rand::{
    distributions::Distribution, distributions::Uniform, rngs::ThreadRng, seq::SliceRandom, Rng,
};
use sapphire::reader2;
use sapphire::utility::SaHashSet;
use std::fs::File;
use std::io;
use std::io::Write;
use tempus_fugit::measure;

macro_rules! write_single_inst {
    ($i:expr, $rng:expr, $file:expr, $inst_dist:expr, $ty_dist:expr, $i8s:expr, $i16s:expr, $i32s:expr, $i64s:expr) => {{
        let opc = match $inst_dist.sample(&mut $rng) {
            0 => "iadd",
            1 => "isub",
            2 => "imul",
            3 => "sdiv",
            4 => "udiv",
            5 => "srem",
            6 => "urem",
            7 => "and",
            8 => "or",
            9 => "xor",
            10 => "shl",
            11 => "ashr",
            12 => "lshr",
            _ => unreachable!(),
        };

        let (ty, vec) = match $ty_dist.sample(&mut $rng) {
            0 => ("i8", &mut $i8s),
            1 => ("i16", &mut $i16s),
            2 => ("i32", &mut $i32s),
            3 => ("i64", &mut $i64s),
            _ => unreachable!(),
        };

        let last = vec[vec.len() - 1];
        let second_to_last = vec[vec.len() - 2];
        let line = format!("  %{} = {opc} {ty} %{second_to_last}, %{last}\n", $i);

        $file.write_all(line.as_bytes())?;

        vec.push($i);
    }};
}

fn generate_name(rng: &mut ThreadRng) -> String {
    const ALPHABET: &'static [u8] =
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz1234567890_.";

    loop {
        let mut name = String::default();

        for _ in 0..rng.gen_range(5..15) {
            name.push(ALPHABET.choose(rng).copied().unwrap() as char);
        }

        if name.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) {
            break name;
        }
    }
}

fn generate_sir() -> io::Result<()> {
    let mut seen = SaHashSet::default();
    let mut rng = thread_rng();
    let mut file = File::create("/tmp/generated.sir")?;

    let mut i8s = vec![2, 3];
    let mut i16s = vec![4, 5];
    let mut i32s = vec![0, 1];
    let mut i64s = vec![6, 7];

    file.write_all(b"fn void @test(i32, i32) {\n")?;
    file.write_all(b"entry(i32 %0, i32 %1):\n")?;
    file.write_all(b"  %2 = trunc i8, i32 %0\n")?;
    file.write_all(b"  %3 = trunc i8, i32 %1\n")?;
    file.write_all(b"  %4 = trunc i16, i32 %0\n")?;
    file.write_all(b"  %5 = trunc i16, i32 %1\n")?;
    file.write_all(b"  %6 = sext i64, i32 %0\n")?;
    file.write_all(b"  %7 = zext i64, i32 %1\n")?;

    let inst_dist = Uniform::<i32>::new_inclusive(0, 12);
    let ty_dist = Uniform::<i32>::new_inclusive(0, 3);
    let param_dist = Uniform::<i32>::new_inclusive(0, 10);

    // generate an initial set of instructions, fill up our lists of values
    for i in 8..100 {
        write_single_inst!(i, rng, file, inst_dist, ty_dist, i8s, i16s, i32s, i64s);
    }

    let mut i = 100;

    while i <= 2_000_000 {
        // end the block roughly every 15 instructions, generate a new one and branch
        // to that new block. new block will have random amount of parameters
        if rng.gen_ratio(1, 15) {
            let name = loop {
                let n = generate_name(&mut rng);

                if !seen.contains(&n) {
                    break n;
                }
            };

            seen.insert(name.clone());

            let n_params = param_dist.sample(&mut rng);

            if n_params == 0 {
                file.write_all(format!("  br {name}\n").as_bytes())?;
                file.write_all(format!("{name}:\n").as_bytes())?;
            } else {
                let mut args = String::default();
                let mut params = String::default();

                for j in 0..(n_params as usize) {
                    let (ty, vec) = match ty_dist.sample(&mut rng) {
                        0 => ("i8", &mut i8s),
                        1 => ("i16", &mut i16s),
                        2 => ("i32", &mut i32s),
                        3 => ("i64", &mut i64s),
                        _ => unreachable!(),
                    };

                    args += &format!("{ty} %{}", vec[vec.len() - j - 1]);
                    params += &format!("{ty} %{}", (i as usize) + j);

                    if j != (n_params as usize) - 1 {
                        args += ", ";
                        params += ", ";
                    }
                }

                file.write_all(format!("  br {name}({args})\n").as_bytes())?;
                file.write_all(format!("{name}({params}):\n").as_bytes())?;

                i += n_params;
            }
        } else {
            write_single_inst!(i, rng, file, inst_dist, ty_dist, i8s, i16s, i32s, i64s);

            i += 1;
        }
    }

    file.write_all(b"  ret void\n")?;
    file.write_all(b"}\n")?;

    Ok(())
}

fn main() -> io::Result<()> {
    let file = std::env::args().skip(1).next().unwrap();

    if file == "--generate" {
        generate_sir()?;

        return Ok(());
    }

    let source = std::fs::read_to_string(&file)?;

    let (module, reader2) = measure! {{
        let module = reader2::parse_sir(&file, &source);

        std::hint::black_box(module)
    }};

    println!("reader2 took {reader2}\n\n");

    match module {
        Ok(_) => {}
        Err(e) => println!("{e}"),
    }

    Ok(())
}
