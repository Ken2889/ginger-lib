use super::Group;

/// Generic struct of a formal linear combination
pub struct LinearCombination<G: Group>
{
    pub items: Vec<(G::ScalarField, G)>
}

impl<G: Group> LinearCombination<G>
{
    /// Consturcts general LC
    pub fn new(items: Vec<(G::ScalarField, G)>) -> Self {
        LinearCombination {
            items
        }
    }

    /// Add term to LC
    pub fn push(&mut self, coeff: G::ScalarField, item: G) {
        self.items.push((coeff, item))
    }

    /// Combine LC
    pub fn combine(&self) -> G {
        let mut combined = G::zero();
        for (coeff, item) in self.items.iter() {
            combined += &(item.clone() * coeff)
        }
        combined
    }
}