use once_cell::unsync::OnceCell;
use std::fmt;
use std::ops::Index;
use std::result::Result;

/// SteadyVec<T> is a variant of std::Vec<T> which does
/// not ever move it's contents, meaning that it's safe to hold
/// interior references while appending to it.
///
/// The performance guarantees of this structure are asymptotically
/// equivalent to a standard resizing vector using size doubling. However,
/// indexing requires two pointer dereferences rather than one, and
/// growing the vector only requires allocation, not copying.
#[derive(Debug)]
pub struct SteadyVec<T> {
    // the capacities of the vectors in this array are
    // 1, 1, 2, 2^1, 2^2, ..., 2^63, giving it a total
    // potential capacity of 2^64, and the capacity of
    // vectors before each index 2^(i-1)
    data: [OnceCell<Vec<OnceCell<T>>>; 65],
}

fn items_before_outer_index(index: usize) -> u64 {
    if index == 0 {
        0
    } else {
        2_u64.pow((index - 1) as u32)
    }
}

fn items_at_outer_index(index: usize) -> u64 {
    if index == 0 {
        1
    } else {
        2_u64.pow((index - 1) as u32)
    }
}

impl<T> SteadyVec<T> {
    const NONE: OnceCell<Vec<OnceCell<T>>> = OnceCell::new();

    pub const fn new() -> Self {
        SteadyVec {
            data: [Self::NONE; 65],
        }
    }

    pub fn get(&self, index: u64) -> Option<&T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index]
            .get()
            .and_then(|i| i[inner_index].get())
    }

    pub fn try_set(&self, index: u64, item: T) -> Result<(), &T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index].get_or_init(|| {
            let size = usize::try_from(items_at_outer_index(outer_index))
                .expect("index too big for architecture!");
            (0..size).map(|_| OnceCell::new()).collect()
        })[inner_index]
            .try_insert(item)
            .map(|_| ())
            .map_err(|t| t.0)
    }

    pub fn iter<'a>(&'a self) -> SteadyVecIterator<'a, T> {
        return SteadyVecIterator {
            underlying: self,
            index: 0,
        };
    }
}

pub struct SteadyVecIterator<'a, T> {
    underlying: &'a SteadyVec<T>,
    index: u64,
}

impl<'a, T> Iterator for SteadyVecIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let it = self.underlying.get(self.index);
        self.index += 1;
        return it;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn append_while_iterating() {
        let vec: SteadyVec<i32> = SteadyVec::new();

        vec.try_set(0, 0).unwrap();
        vec.try_set(1, 1).unwrap();

        for (idx, (before, last)) in vec.iter().zip(vec.iter().skip(1)).enumerate().take(20) {
            vec.try_set(idx as u64 + 2, before + last).unwrap();
        }

        assert_eq!(
            vec.iter().copied().collect::<Vec<i32>>(),
            vec![
                0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181,
                6765, 10946
            ]
        )
    }
}
