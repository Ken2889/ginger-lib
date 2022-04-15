use crate::Group;

pub trait DualCycle<GDual: Group>:
    Group<BaseField = <GDual as Group>::ScalarField, ScalarField = <GDual as Group>::BaseField>
{
}

impl<G, GDual> DualCycle<GDual> for G
where
    G: Group<BaseField = <GDual as Group>::ScalarField, ScalarField = <GDual as Group>::BaseField>,
    GDual: Group,
{
}
