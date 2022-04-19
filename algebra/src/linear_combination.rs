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
        // Nothing to combine for empty LC
        if self.items.is_empty() {
            return E::zero();
        }

        // Specific initialization of the combined value (saves at least an addition)
        let mut combined = if self.items[0].0.is_one() {
            self.items[0].1.clone() // Coeff is one, so we can return the item directly
        } else {
            self.items[0].1.clone() * &self.items[0].0 // (c0 * e0)
        };

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

#[cfg(all(test, feature = "tweedle"))]
mod test {
    use rand::thread_rng;

    use super::*;
    use crate::{
        fields::tweedle::Fr,
        curves::tweedle::dee::DeeJacobian as TweedleDee, UniformRand, Group, GroupVec
    };

    const MAX_LENGTH: usize = 10;

    /// Initialize a random LC of scalars and points and checks that the result of combine is indeed
    /// given by (scalar_0 * point_0) + ... + (scalar_n-1 * point_n-1) 
    fn test_scalar_point_random_lc_combine<G: Group>(scalars: Vec<G::ScalarField>, points: Vec<G>) {
        let raw_lc = scalars
            .clone()
            .into_iter()
            .zip(
                points
                    .iter()
            )
            .collect::<Vec<_>>();

        // Initialize LC and combine
        let lc = LinearCombination::new(raw_lc);
        let combined_value = lc.combine();

        // Compute the LC manually, instead, and check that the combined value is indeed the sum of the scalars times the points
        let expected_combined_value = scalars
            .into_iter()
            .zip(
                points
                    .into_iter()
            )
            .map(|(scalar, point)| point * &scalar)
            .fold(G::zero(), |acc, val| acc + val);

        assert_eq!(combined_value, expected_combined_value);
    }

    /// Initialize a random LC from a single batching scalar and a vector of  points and checks that the result of combine is indeed
    /// given by (1 * point_0) + (scalar * point_1) + (scalar^2 * point_2) + ... + (scalar^n-1 * point_n-1) 
    fn test_scalar_point_algebraic_lc_combine<G: Group>(batching_scalar: G::ScalarField, points: Vec<G>) {
        let points_ref = points.iter().collect::<Vec<_>>();

        // Initialize LC and combine
        let lc = LinearCombination::new_from_val(&batching_scalar, points_ref);
        let combined_value = lc.combine();

        // Compute the LC manually, instead, and check that the combined value is indeed the sum of the scalars times the points
        let mut batching_scalar_pows = vec![G::ScalarField::one()];
        (1..points.len())
            .for_each(|i| {
                batching_scalar_pows.push(batching_scalar_pows[i - 1] * &batching_scalar);
            });
        let expected_combined_value = batching_scalar_pows
            .into_iter()
            .zip(
                points
                    .into_iter()
            )
            .map(|(scalar, point)| point * &scalar)
            .fold(G::zero(), |acc, val| acc + val);

        assert_eq!(combined_value, expected_combined_value);
    }

    #[test]
    fn test_scalar_point_lc() {
        let rng = &mut thread_rng();

        // Generate random scalars and points
        let scalars = (0..MAX_LENGTH)
            .map(|_| Fr::rand(rng))
            .collect::<Vec<_>>();
        let points = (0..MAX_LENGTH)
            .map(|_| TweedleDee::rand(rng))
            .collect::<Vec<_>>();

        // Execute tests
        let batching_scalar = scalars[0];
        test_scalar_point_random_lc_combine(scalars, points.clone());
        test_scalar_point_algebraic_lc_combine(batching_scalar, points)
    }

    #[test]
    fn test_scalar_point_vec_lc() {
        let rng = &mut thread_rng();

        // Generate random scalars and points
        let scalars = (0..MAX_LENGTH)
            .map(|_| Fr::rand(rng))
            .collect::<Vec<_>>();
        let points = (0..MAX_LENGTH)
            .map(|_| GroupVec::<TweedleDee>::rand(MAX_LENGTH as u16, rng))
            .collect::<Vec<_>>();

        // Execute tests
        let batching_scalar = scalars[0];
        test_scalar_point_random_lc_combine(scalars, points.clone());
        test_scalar_point_algebraic_lc_combine(batching_scalar, points)
    }
}