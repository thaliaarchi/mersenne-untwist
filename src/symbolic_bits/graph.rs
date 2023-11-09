use std::fmt::{self, Debug, Display, Formatter};

use crate::{
    symbolic_bits::{Bit, State, Var, Version},
    N,
};

#[derive(Clone)]
pub struct Graph {
    adjacent: Vec<Vec<Var>>,
}

impl Graph {
    pub fn from_state(state: &State) -> Self {
        let mut adjacent = Vec::with_capacity(N * 32);
        for (i, value) in state.values.iter().enumerate() {
            assert_eq!(state.versions[i], Version::S1);
            for bit in value.bits.iter() {
                let mut edges = Vec::new();
                push_edges(bit, &mut edges);
                assert!(!edges.is_empty());
                adjacent.push(edges);
            }
        }
        Graph { adjacent }
    }
}

fn push_edges(bit: &Bit, edges: &mut Vec<Var>) {
    match bit {
        Bit::Const(_) => panic!("unexpected const"),
        Bit::Ref(v) => edges.push(*v),
        Bit::Xor(x, y) => {
            push_edges(x, edges);
            push_edges(y, edges);
        }
    }
}

impl Debug for Graph {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, edges) in self.adjacent.iter().enumerate() {
            let (first, rest) = edges.split_first().unwrap();
            write!(f, "s1.{}.{} = {first}", i / 32, i % 32)?;
            for node in rest {
                write!(f, " ^ {node}")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Display for Graph {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "digraph mt19937_state {{")?;
        for (i, edges) in self.adjacent.iter().enumerate() {
            for node in edges {
                writeln!(f, "    \"s1.{}.{}\" -> \"{node}\";", i / 32, i % 32)?;
            }
        }
        writeln!(f, "}}")
    }
}
