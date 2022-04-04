    // DDT: It could be better to define it as number of ADDENDS over normal form.
    //      In this case the minimum possible value should be 1, num_add(a+b) = num_add(a) + num_add(b), num_add(a*b)= num_add(a) * num_add(b).
    //      Also the definition of the surfeit would be more natural.
        // DDT: The notation used in this function is not in accordance with notation used elsewhere. This can cause some confusion
    //      shift_per_limb = bits_per_limb in the NonNativeFieldGadget,
    //      bits_per_limb defined as "number of bits" does not make too much sense: number of bits of what?
    //      It looks to be the 2*shift_per_limb, since the limbsize of a product is 2*bits_per_limb + surfeit(product) in the NonNative notation.