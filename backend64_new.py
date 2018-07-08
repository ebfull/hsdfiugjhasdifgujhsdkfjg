MODULUS_NUM = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
MODULUS_BITS = 381
LIMB_SIZES = [55, 55, 51, 55, 55, 55, 55]
WORD_SIZE = 64

# Check that MODULUS_BITS is correct
assert(2**MODULUS_BITS > MODULUS_NUM)
assert(2**(MODULUS_BITS - 1) < MODULUS_NUM)

# Check that limb sizes are correct
tmp = 0
for i in range(0, len(LIMB_SIZES)):
	assert(LIMB_SIZES[i] < WORD_SIZE)
	tmp += LIMB_SIZES[i]
assert(tmp == MODULUS_BITS)

# Compute the value of the modulus in this representation
MODULUS = []
tmp = MODULUS_NUM
print("MODULUS = [")
for i in range(0, len(LIMB_SIZES)):
	this_modulus_num = tmp & ((2**LIMB_SIZES[i]) - 1)
	MODULUS.append(this_modulus_num)
	tmp = tmp >> LIMB_SIZES[i]
	print("\t", hex(this_modulus_num), ",")
print("]")

# Each word in our representation has an associated "magnitude" M
# in which the word is guaranteed to be less than or equal to (2^LIMB_SIZE - 1)*M
# Initialize LARGEST_MAGNITUDE_CARRIES to some high number
LARGEST_MAGNITUDE_CARRIES = 2**WORD_SIZE - 1

for i in range(0, len(LIMB_SIZES)):
	largest_mag = int(2**WORD_SIZE / (2**LIMB_SIZES[i]))
	assert((((2**LIMB_SIZES[i]) - 1)*largest_mag) < 2**WORD_SIZE)
	assert((((2**LIMB_SIZES[i]) - 1)*(largest_mag+1)) > 2**WORD_SIZE)
	if LARGEST_MAGNITUDE_CARRIES > largest_mag:
		LARGEST_MAGNITUDE_CARRIES = largest_mag

print("Largest magnitude allowed for carries:", LARGEST_MAGNITUDE_CARRIES)

NEGATION_MULTIPLES_OF_MODULUS = 0
for i in range(0, len(LIMB_SIZES)):
	tmp = 0
	while (tmp * MODULUS[i]) <= ((2**LIMB_SIZES[i]) - 1):
		tmp = tmp + 1

	if NEGATION_MULTIPLES_OF_MODULUS < tmp:
		NEGATION_MULTIPLES_OF_MODULUS = tmp

print("Scale necessary for negations:", NEGATION_MULTIPLES_OF_MODULUS)
