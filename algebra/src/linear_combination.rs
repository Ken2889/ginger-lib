use num_traits::{Zero, One};
use std::ops::{AddAssign, Mul, MulAssign};

/// Generic struct of a formal linear combination
pub struct LinearCombination<
    'a,
    C: Copy + Eq + PartialEq + Zero + One + for<'b> MulAssign<&'b C>,
    E: Clone + Eq + PartialEq + Zero + for<'b>AddAssign<&'b E> + for<'b> Mul<&'b C, Output = E>,
>
{
    items: Vec<(C, &'a E)>
}

impl<'a, C, E> LinearCombination<'a, C, E>
where
    C: Copy + Eq + PartialEq + Zero + One + for<'b> MulAssign<&'b C>,
    E: Clone + Eq + PartialEq + Zero + for<'b>AddAssign<&'b E> + for<'b> Mul<&'b C, Output = E>,
{
    /// Consturcts general LC
    pub fn new(items: Vec<(C, &'a E)>) -> Self {
        Self {
            items
        }
    }

    /// Constructs empty LC
    pub fn empty() -> Self {
        Self {
            items: vec![]
        }
    }

    /// Get LC length
    pub fn length(&self) -> usize {
        self.items.len()
    }

    /// Constructs LC where the coefficients are the powers of 'batching_val'
    pub fn new_from_val(batching_val: &C, terms: Vec<&'a E>) -> Self {
        let mut coeff = C::one();
        // Nothing to save if there is no element in the LC or if
        // the coefficients will be all 0.
        let items = if terms.is_empty() || batching_val.is_zero() {
            vec![]
        // If batching_val is one, coefficients will be all one,
        // so nothing to do here too
        } else if batching_val.is_one(){
            terms
                .into_iter()
                .map(|term| (coeff, term))
                .collect()
        } else {
            let mut items = vec![(coeff, terms[0])];
            items.append(&mut terms
                .into_iter()
                .skip(1)
                .map(|term| {
                    coeff *= batching_val;
                    (coeff, term)
                })
                .collect());
            items
        };

        Self {
            items
        }
    }

    /// Add term to LC
    pub fn push(&mut self, coeff: C, item: &'a E) {
        // If one of them is zero then nothing to add to the LC really
        if !coeff.is_zero() && !item.is_zero() {
            self.items.push((coeff, item))
        }
    }

    /// Combine LC
    pub fn combine(self) -> E {
        let mut combined = E::zero();

        // Small optimization: check first element, if coeff is one,
        // then we don't need to perform the addition
        if !self.items.is_empty(){
            if self.items[0].0.is_one() {
                combined = self.items[0].1.clone();
            } else {
                combined += self.items[0].1;
            }
        } 

        // Compute (c_0 * e_0) + ... + (c_n * e_n) 
        for (coeff, item) in self.items.into_iter().skip(1) {
            if coeff.is_one() {
                combined += item;
            } else {
                combined += &(item.clone() * &coeff);
            }
        }
        combined
    }
}