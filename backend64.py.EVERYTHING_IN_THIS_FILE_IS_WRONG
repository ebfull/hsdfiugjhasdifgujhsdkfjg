# BLS12-381 modulus
q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

MODULUS_BITS = 381
assert(2**MODULUS_BITS > q)
assert(2**(MODULUS_BITS - 1) < q)

# We're going to use 8 48-bit limbs to represent our elements.
# The final (most significant) limb will be 45 bits.
NUM_LIMBS = 8
LIMB_BITS = 48
FINAL_LIMB_BITS = 45
LIMB_BITS_MASK = (1 << LIMB_BITS) - 1
FINAL_LIMB_BITS_MASK = (1 << FINAL_LIMB_BITS) - 1

# Check that our limb sizes are correct
assert((LIMB_BITS * (NUM_LIMBS - 1) + FINAL_LIMB_BITS) == MODULUS_BITS)
assert(FINAL_LIMB_BITS < LIMB_BITS)

# We're going to use 64-bit words throughout our implementation.
LIMB_WORD_BITS = 64

assert(LIMB_WORD_BITS > LIMB_BITS)
assert(LIMB_WORD_BITS > FINAL_LIMB_BITS)

# Let's get the value of the modulus in this representation. (Little-endian.)
MODULUS = [(q >> (LIMB_BITS*x)) & LIMB_BITS_MASK for x in range(0, NUM_LIMBS)]

# Each element has an associated "magnitude" `M` which guarantees that
# each limb represents a value less than or equal to M * (2^LIMB_BITS - 1)
# (or in the case of the final limb, M * (2^FINAL_LIMB_BITS - 1))
# This is the largest allowed magnitude.
# LARGEST_MAGNITUDE = 65536
LARGEST_MAGNITUDE = 53257

# Let's check that each limb can be of this magnitude without overflowing
# our word.
assert((LARGEST_MAGNITUDE * FINAL_LIMB_BITS_MASK) < 2**LIMB_WORD_BITS)
assert((LARGEST_MAGNITUDE * LIMB_BITS_MASK) < 2**LIMB_WORD_BITS)

# We want to implement negation of an element of magnitude `M` by adding
# a multiple of the modulus and subtracting. Let's see how many multiples
# are needed to ensure the modulus' limbs have a value larger than LIMB_BITS_MASK
NEGATION_MULTIPLES_OF_MODULUS = 4
for i in range(0, NUM_LIMBS):
    if i == (NUM_LIMBS - 1):
        assert((MODULUS[i] * NEGATION_MULTIPLES_OF_MODULUS) > FINAL_LIMB_BITS_MASK)
    else:
        assert((MODULUS[i] * NEGATION_MULTIPLES_OF_MODULUS) > LIMB_BITS_MASK)

# If we have an element in this representation that we'd like to reduce mod
# q, the first step will be to propagate the carry bits through the limbs.
# Let's ensure that this can never result in overflows in the worst case
# that our element involves limbs of the largest value.
carry = 0
largest_limb = 0
for i in range(0, NUM_LIMBS):
    v = 0
    if i == (NUM_LIMBS - 1):
        v = (LARGEST_MAGNITUDE * FINAL_LIMB_BITS_MASK) + carry
    else:
        v = (LARGEST_MAGNITUDE * LIMB_BITS_MASK) + carry
    assert(v < 2**LIMB_WORD_BITS)
    carry = v >> LIMB_BITS
    if i == (NUM_LIMBS - 1):
        largest_limb = v

# Compute the largest number represented by a magnitude 2 element
MAX_MAG_2 = 0
for i in range(0, NUM_LIMBS):
    limb_bits = 0
    if i == (NUM_LIMBS - 1):
        limb_bits = FINAL_LIMB_BITS
    else:
        limb_bits = LIMB_BITS

    MAX_MAG_2 = MAX_MAG_2 + ((2 * ((2**limb_bits) - 1)) << (i*LIMB_BITS))

# Easier way to calculate this
assert(MAX_MAG_2 == ((2**MODULUS_BITS - 1)*2))

# We also know a shorthand for computing the maximum carry value for any
# element of magnitude M
for i in range(0, LARGEST_MAGNITUDE):
    assert(((2**MODULUS_BITS - 1)*i >> MODULUS_BITS) == (((2**FINAL_LIMB_BITS - 1)*i) >> FINAL_LIMB_BITS))

# TODO: Who cares? We may not need this ever.
# We know that up to a magnitude of 5, the maximum carry value will be 4
assert((((2**MODULUS_BITS - 1)*5) >> MODULUS_BITS) == 4)
assert((((2**MODULUS_BITS - 1)*6) >> MODULUS_BITS) == 5)

# Montgomery reduction constant R
R = 2**384
assert(R > q)

# Can we perform a montgomery reduction of the product of any two
# magnitude 2 elements with this constant R?
assert((MAX_MAG_2 * MAX_MAG_2) < (q*R))

# When we're reducing a field element (trying to reduce its magnitude) we
# need to know how many times to "subtract" q from it. We can do this by
# grabbing the most significant bits from the final limb (more significant
# than the modulus) and dividing them by the modulus
largest_carry = largest_limb >> FINAL_LIMB_BITS

for carry in range(0, largest_carry+1):
    # How many times _can_ we subtract q from the smallest element with
    # this carry before underflowing?
    tmp = carry << MODULUS_BITS
    times_we_can_subtract = tmp // q

    # Check that our result is correct
    assert((tmp - (q*times_we_can_subtract)) >= 0)
    assert((tmp - (q*(times_we_can_subtract+1))) < 0)

    # How many times _must_ we subtract q from the largest element with
    # this carry in order to ensure it is magnitude 2?
    # tmp - xq < MAX_MAG_2
    # tmp - MAX_MAG_2 < xq
    # (tmp - MAX_MAG_2) / q < x
    tmp = (carry << MODULUS_BITS) | ((2**MODULUS_BITS) - 1)
    times_we_must_subtract = ((tmp - MAX_MAG_2) // q) + 1
    if times_we_must_subtract < 0:
        times_we_must_subtract = 0

    # Check that our result is correct
    assert((tmp - (q*times_we_must_subtract)) < MAX_MAG_2)
    if times_we_must_subtract != 0:
        assert((tmp - (q*(times_we_must_subtract-1))) >= MAX_MAG_2)

    # Let's make sure we can always safely subtract enough.
    assert(times_we_can_subtract >= times_we_must_subtract)

    # This is how we will determine the number of times to subtract
    # during our reduction step. Let's confirm it works for all cases.
    assert(((carry << FINAL_LIMB_BITS) // MODULUS[NUM_LIMBS - 1]) == times_we_can_subtract)

    # We can rely on the carry value to help us decide how to reduce without
    # performing the previous division, but only up to a carry of 4.
    if carry <= 4:
        assert(carry == times_we_can_subtract)

    # During the reduction, we'll need to subtract multiples of the modulus
    # from each limb with borrow bits set. Let's make sure we can do this without
    # underflowing
    borrow = 0
    for i in range(0, NUM_LIMBS):
        # How many bits are in this limb
        limb_bits = 0
        if i == (NUM_LIMBS - 1):
            limb_bits = FINAL_LIMB_BITS
        else:
            limb_bits = LIMB_BITS

        # The borrow bits that are used during reduction
        borrow_bits = (2**(LIMB_WORD_BITS - limb_bits)) - 1
        # The minimum sized limb value with borrow bits set
        min_limb = borrow_bits << limb_bits

        # Subtract a multiple from the modulus and then the borrow
        # from the previous limb
        tmp = (min_limb - (MODULUS[i] * times_we_can_subtract)) - borrow

        # No underflowing!
        assert(tmp > 0)

        # Propagate borrow (which should be maximal)
        borrow = borrow_bits - (tmp >> limb_bits)
        
