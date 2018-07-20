q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
goal = (q-1)*9

def f(x):
	return (x * 0b10000000000000000000000000000000000000000000000000000000000000000) >> 64
                                                                                   #
for mag in range(0, 10):
	largest = ((q-1)*mag) + (q*10)
	carry = largest >> 381
	smallest = (q*10)

	x = 0
	acc = largest
	while acc > goal:
		acc = acc - q
		x = x + 1

	lol = f(carry)
	assert((smallest - (x*q)) >= 0)
	assert((largest - (x*q)) <= goal);
	print("magnitude", mag, "has carry", carry, "and x=", x, "and f(x)=", lol)

