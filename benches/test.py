q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
goal = (q-1)*3

def f(x):
	return x + 1

for mag in range(0, 10):
	largest = ((q-1)*mag) + (q*10)
	carry = largest >> 381
	smallest = carry << 381

	x = 0
	acc = largest
	while acc > goal:
		acc = acc - q
		x = x + 1

	lol = f(carry)
	print("magnitude", mag, "has carry", carry, "and x=", x, "and f(x)=", lol)

	assert((largest - (lol*q)) <= goal);
	assert((smallest - (lol*q)) >= 0)

