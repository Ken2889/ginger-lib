use super::Group;
use crate::fields::Field;

/// Generic struct of a formal linear combination
pub struct LinearCombination<'a, G: Group>
{
    items: Vec<(G::ScalarField, &'a G)>
}

impl<'a, G: Group> LinearCombination<'a, G>
{
    /// Consturcts general LC
    pub fn new(items: Vec<(G::ScalarField, &'a G)>) -> Self {
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
    pub fn new_from_val(batching_val: &G::ScalarField, terms: Vec<&'a G>) -> Self {
        let mut coeff = G::ScalarField::one();
        let items = if terms.is_empty() {
            vec![]
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
    pub fn push(&mut self, coeff: G::ScalarField, item: &'a G) {
        self.items.push((coeff, item))
    }

    /// Combine LC
    pub fn combine(self) -> G {
        let mut combined = G::zero();
        for (coeff, item) in self.items.into_iter() {
            combined += &(item.clone() * &coeff)
        }
        combined
    }
}