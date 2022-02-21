use std::cmp::Ordering;
use std::ops::{Index, IndexMut};
use std::result::Result;

// TODO: Duplicate all this code, or maybe use a macro,
// to also create a sync implementation
use once_cell::unsync::OnceCell;

/// SteadyVec<T> is a variant of std::Vec<T> which does
/// not ever move it's contents, meaning that it's safe to hold
/// interior references while appending to it.
///
/// The performance guarantees of this structure are asymptotically
/// equivalent to a standard resizing vector using size doubling. However,
/// indexing requires two pointer dereferences rather than one, and
/// growing the vector only requires allocation, not copying.
///
/// One important difference in the API between this type and Vec<T>
/// is that this type allows non-contoiguous ranges of set values. For example,
/// while it is illegal to have a Vec<T> have a value at index 0 and at index 2
/// with no value at index 1, that state is legal for this vector. That means
/// that SteadyVec::iter does not return a FusedIterator, and that this
/// type has no inherent notion of length. Doing this gives slightly more
/// flexibility in the exact order in which values are initialized. For
/// a type that does not move it's contents but which has these constraints,
/// see SteadyStack<T>.
#[derive(Debug, PartialEq, Eq)]
pub struct SteadyVec<T> {
    // the capacities of the vectors in this array are
    // 1, 1, 2, 2^1, 2^2, ..., 2^63, giving it a total
    // potential capacity of 2^64, and the capacity of
    // vectors before each index 2^(i-1)
    data: [OnceCell<Vec<OnceCell<T>>>; 65],
}

impl<T: PartialOrd> PartialOrd for SteadyVec<T> {
    fn partial_cmp(&self, other: &SteadyVec<T>) -> Option<Ordering> {
        for (x, y) in self.data.iter().zip(other.data.iter()) {
            match (x.get(), y.get()) {
                (None, None) => {}
                (Some(_), None) => return Some(Ordering::Greater),
                (None, Some(_)) => return Some(Ordering::Less),
                (Some(xs), Some(ys)) => {
                    for (x, y) in xs.iter().zip(ys.iter()) {
                        match (x.get(), y.get()) {
                            (None, None) => {}
                            (Some(_), None) => return Some(Ordering::Greater),
                            (None, Some(_)) => return Some(Ordering::Less),
                            (Some(a), Some(b)) => match a.partial_cmp(b) {
                                Some(Ordering::Less) => return Some(Ordering::Less),
                                Some(Ordering::Greater) => return Some(Ordering::Greater),
                                Some(Ordering::Equal) => {}
                                None => return None,
                            },
                        }
                    }
                }
            }
        }

        return Some(Ordering::Equal);
    }
}

impl<T: Ord> Ord for SteadyVec<T> {
    fn cmp(&self, other: &SteadyVec<T>) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
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

    /// try_set returns Ok(()) if the index didn't have a value, and Err(&x) if
    /// the index already had a value, with &x being a reference to the value
    /// in that index.
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

    /// try_init executes f only if the index has no value. The return value is the
    /// same as try_set.
    pub fn try_init(&self, index: u64, f: impl FnOnce() -> T) -> Result<(), &T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        let cell = &self.data[outer_index].get_or_init(|| {
            let size = usize::try_from(items_at_outer_index(outer_index))
                .expect("index too big for architecture!");
            (0..size).map(|_| OnceCell::new()).collect()
        })[inner_index];

        match cell.get() {
            Some(t) => Err(t),
            None => {
                cell.get_or_init(f);
                Ok(())
            }
        }
    }

    /// get_or_set returns a reference to the value at the index, setting it
    /// to the provided value if needed.
    pub fn get_or_set(&self, index: u64, item: T) -> &T {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index].get_or_init(|| {
            let size = usize::try_from(items_at_outer_index(outer_index))
                .expect("index too big for architecture!");
            (0..size).map(|_| OnceCell::new()).collect()
        })[inner_index]
            .get_or_init(|| item)
    }

    /// get_or_init returns a reference to the value at the index, calling f
    /// and setting the value with f's return value if needed.
    pub fn get_or_init(&self, index: u64, f: impl FnOnce() -> T) -> &T {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index].get_or_init(|| {
            let size = usize::try_from(items_at_outer_index(outer_index))
                .expect("index too big for architecture!");
            (0..size).map(|_| OnceCell::new()).collect()
        })[inner_index]
            .get_or_init(f)
    }

    pub fn get_mut(&mut self, index: u64) -> Option<&mut T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index]
            .get_mut()
            .and_then(|i| i[inner_index].get_mut())
    }

    pub fn delete(&mut self, index: u64) -> Option<T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index]
            .get_mut()
            .and_then(|i| i[inner_index].take())
    }

    /// set returns the previous value at the index.
    pub fn set(&mut self, index: u64, item: T) -> Option<T> {
        let outer_index = (u64::BITS - index.leading_zeros()) as usize;
        let inner_index = (index - items_before_outer_index(outer_index)) as usize;

        self.data[outer_index].get_or_init(|| {
            let size = usize::try_from(items_at_outer_index(outer_index))
                .expect("index too big for architecture!");
            (0..size).map(|_| OnceCell::new()).collect()
        });

        self.data[outer_index].get_mut().and_then(|i| {
            let old = i[inner_index].take();
            i[inner_index]
                .set(item)
                .map_err(|_| "this should never happen")
                .unwrap();
            return old;
        })
    }

    pub fn iter<'a>(&'a self) -> SteadyVecIterator<'a, T> {
        return SteadyVecIterator {
            underlying: self,
            index: 0,
        };
    }

    /* TODO: implement this. I'm pretty sure it requries unsafe
    pub fn iter_mut<'a>(&'a mut self) -> SteadyVecMutIterator<'a, T> {
        return SteadyVecMutIterator {
            underlying: self,
            index: 0,
        };
    }
    */

    pub fn into_iter(self) -> SteadyVecOwnedIterator<T> {
        return SteadyVecOwnedIterator {
            underlying: self,
            index: 0,
        };
    }
}

impl<T> FromIterator<T> for SteadyVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut res = SteadyVec::new();

        for (i, x) in iter.into_iter().enumerate() {
            res.set(i as u64, x);
        }

        return res;
    }
}

impl<T> Index<u64> for SteadyVec<T> {
    type Output = T;

    fn index(&self, index: u64) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T> IndexMut<u64> for SteadyVec<T> {
    fn index_mut(&mut self, index: u64) -> &mut Self::Output {
        self.get_mut(index).unwrap()
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

/* TODO: implement this. I'm pretty sure it requries unsafe
pub struct SteadyVecMutIterator<'a, T> {
    underlying: &'a mut SteadyVec<T>,
    index: u64,
}

impl<'a, T> Iterator for SteadyVecMutIterator<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        // lifetime error on next line. See
        // https://www.reddit.com/r/rust/comments/bt1ghr/lifetime_differences_between_mutable_and/
        let it = self.underlying.get_mut(self.index);
        self.index += 1;
        return it;
    }
}
*/

pub struct SteadyVecOwnedIterator<T> {
    underlying: SteadyVec<T>,
    index: u64,
}

impl<T> Iterator for SteadyVecOwnedIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let it = self.underlying.delete(self.index);
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
